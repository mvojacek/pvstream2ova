import hashlib
import inspect
import io
import os
import shutil
import signal
import stat
import struct
import subprocess
import sys
import tarfile
import tempfile
import unittest
import xml.etree.ElementTree as ET
import zlib
from contextlib import ExitStack, contextmanager
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import Mock, call, patch

import pvstream2ova as pv


GRAIN = 65536
ARTIFACT_PARENT = Path("/tmp/maki/pvstream2ova/thin-map-tests")
QEMU_IMG = shutil.which("qemu-img")


def single(origin=1, physical=91):
    return (f'<single_mapping origin_block="{origin}" '
            f'data_block="{physical}" time="2"/>')


def extent(origin=2, length=2, physical=7):
    return (f'<range_mapping origin_begin="{origin}" data_begin="{physical}" '
            f'length="{length}" time="2"/>')


def thin_xml(mappings="", count=0, thin_id=731, sectors=128):
    return (f'<superblock uuid="" time="3" transaction="17" flags="0" '
            f'version="2" data_block_size="{sectors}" nr_data_blocks="1048576" '
            f'metadata_snap="42"><device dev_id="{thin_id}" mapped_blocks="{count}" '
            f'transaction="16" creation_time="1" snap_time="2">{mappings}'
            '</device></superblock>').encode()


class ChunkedStream(io.BytesIO):
    def __init__(self, value, chunk):
        super().__init__(value)
        self.chunk = chunk

    def read(self, size=-1):
        return super().read(self.chunk if size < 0 else min(size, self.chunk))


class TemporaryTestCase(unittest.TestCase):
    def setUp(self):
        ARTIFACT_PARENT.mkdir(parents=True, exist_ok=True)
        temporary = tempfile.TemporaryDirectory(dir=ARTIFACT_PARENT)
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)

    def source(self, size, pieces=(), name="source.raw"):
        path = self.directory / name
        with path.open("wb") as stream:
            stream.truncate(size)
            for offset, data in pieces:
                self.assertLessEqual(offset + len(data), size)
                stream.seek(offset)
                stream.write(data)
        return path


def decode_vmdk(test, data, size):
    test.assertEqual(len(data) % 512, 0)
    test.assertGreaterEqual(len(data), 128 * 512 + 5 * 512)
    capacity = size // 512
    n_grains = (size + GRAIN - 1) // GRAIN
    n_tables = (n_grains + 511) // 512

    def header(offset, directory):
        test.assertEqual(struct.unpack_from("<III", data, offset),
                         (0x564D444B, 3, 0x30001))
        test.assertEqual(struct.unpack_from("<QQQQI", data, offset + 12),
                         (capacity, 128, 1, 20, 512))
        test.assertEqual(struct.unpack_from("<QQQ", data, offset + 48),
                         (0, directory, 128))
        test.assertEqual(data[offset + 73:offset + 77], b"\n \r\n")
        test.assertEqual(struct.unpack_from("<H", data, offset + 77)[0], 1)

    def marker(offset, sectors, kind):
        test.assertEqual(struct.unpack_from("<QII", data, offset), (sectors, 0, kind))
        test.assertEqual(data[offset + 16:offset + 512], bytes(496))

    header(0, (1 << 64) - 1)
    test.assertIn(f"RDONLY {capacity} STREAMOPTIMIZED".encode(), data[512:21 * 512])
    test.assertEqual(data[21 * 512:128 * 512], bytes(107 * 512))
    marker(len(data) - 1536, 1, 3)
    marker(len(data) - 512, 0, 0)
    gd_sector = struct.unpack_from("<Q", data, len(data) - 1024 + 56)[0]
    header(len(data) - 1024, gd_sector)
    gd_sectors = (n_tables * 4 + 511) // 512
    marker((gd_sector - 1) * 512, gd_sectors, 2)
    test.assertEqual((gd_sector + gd_sectors) * 512, len(data) - 1536)
    directory = struct.unpack_from(f"<{n_tables}I", data, gd_sector * 512)
    test.assertEqual(data[gd_sector * 512 + n_tables * 4:(gd_sector + gd_sectors) * 512],
                     bytes(gd_sectors * 512 - n_tables * 4))
    grains = {}
    offsets = {}
    tables = []
    lbas = []
    position = 128 * 512
    while position < (gd_sector - 1) * 512:
        lba, compressed_size = struct.unpack_from("<QI", data, position)
        if compressed_size:
            test.assertEqual(lba % 128, 0)
            grain = lba // 128
            test.assertLess(grain, n_grains)
            test.assertEqual(grain // 512, len(tables))
            test.assertNotIn(grain, grains)
            payload = data[position + 12:position + 12 + compressed_size]
            decoder = zlib.decompressobj()
            raw = decoder.decompress(payload) + decoder.flush()
            test.assertTrue(decoder.eof)
            test.assertEqual(decoder.unused_data, b"")
            test.assertEqual(len(raw), GRAIN)
            test.assertTrue(any(raw))
            grains[grain] = raw
            offsets[grain] = position // 512
            lbas.append(lba)
            end = position + 12 + compressed_size
            padded_end = (end + 511) // 512 * 512
            test.assertEqual(data[end:padded_end], bytes(padded_end - end))
            position = padded_end
        else:
            marker(position, 4, 1)
            test.assertEqual(directory[len(tables)], position // 512 + 1)
            entries = struct.unpack_from("<512I", data, position + 512)
            start = len(tables) * 512
            test.assertEqual(entries, tuple(offsets.get(start + i, 0) for i in range(512)))
            tables.append(entries)
            position += 5 * 512
    test.assertEqual(position, (gd_sector - 1) * 512)
    test.assertEqual(len(tables), n_tables)
    test.assertEqual(lbas, sorted(lbas))
    return SimpleNamespace(grains=grains, tables=tables, directory=directory,
                           lbas=lbas, capacity=capacity)


def assert_logical_contents(test, decoded, size, pieces):
    expected = {}
    for offset, data in pieces:
        end = offset + len(data)
        while offset < end:
            grain, within = divmod(offset, GRAIN)
            length = min(end - offset, GRAIN - within)
            target = expected.setdefault(grain, bytearray(GRAIN))
            target[within:within + length] = data[len(data) - (end - offset):
                                                  len(data) - (end - offset) + length]
            offset += length
    expected = {grain: bytes(raw) for grain, raw in expected.items() if any(raw)}
    test.assertEqual(decoded.grains, expected)
    test.assertEqual(decoded.capacity * 512, size)


class ThinParserTests(unittest.TestCase):
    def parse(self, xml, sectors=128, size=10 * GRAIN, thin_id=731):
        return pv._parse_thin_dump(io.BytesIO(xml), thin_id, sectors, size)

    def test_single_range_fragmentation_and_stream_chunks(self):
        for sectors in (128, 256, 2048, 2097152):
            chunk = sectors * 512
            xml = thin_xml(single(1, 900) + extent(2, 2, 3) + single(6, 17), 4,
                           sectors=sectors)
            for read_size in (1, 7, 127, 16384):
                with self.subTest(sectors=sectors, read_size=read_size):
                    stream = ChunkedStream(xml, read_size)
                    self.assertEqual(pv._parse_thin_dump(stream, 731, sectors, chunk * 10),
                                     [(chunk, 4 * chunk), (6 * chunk, 7 * chunk)])

    def test_mapping_tails_across_read_boundaries(self):
        for mapping, count in ((single(), 1), (extent(1, 2), 2)):
            for following in ("", single(5)):
                expected = [(GRAIN, (1 + count) * GRAIN)]
                if following:
                    expected.append((5 * GRAIN, 6 * GRAIN))
                for tail in ("\n \t", "\n unexpected \t"):
                    xml = thin_xml(mapping + tail + following, count + bool(following))
                    boundary = xml.index(mapping.encode()) + len(mapping)
                    for read_size in (1, 2, 7, 127, boundary - 1, boundary, boundary + 1, 16384):
                        with self.subTest(mapping=mapping, following=following, tail=tail,
                                          read_size=read_size):
                            stream = ChunkedStream(xml, read_size)
                            if tail.strip():
                                with self.assertRaisesRegex(ValueError, "Unexpected text after thin XML element"):
                                    pv._parse_thin_dump(stream, 731, 128, 10 * GRAIN)
                            else:
                                self.assertEqual(pv._parse_thin_dump(stream, 731, 128, 10 * GRAIN),
                                                 expected)

    def test_explicit_empty_and_optional_superblock_attributes(self):
        self.assertEqual(self.parse(thin_xml()), [])
        xml = thin_xml(single(0), 1)
        for attribute in (b' flags="0"', b' version="2"', b' metadata_snap="42"'):
            xml = xml.replace(attribute, b"")
        self.assertEqual(self.parse(xml), [(0, GRAIN)])

    def test_capacity_clipping_does_not_change_mapping_count(self):
        size = 4 * GRAIN + 512
        xml = thin_xml(single(1) + extent(3, 4) + single(100), 6)
        self.assertEqual(self.parse(xml, size=size), [(GRAIN, 2 * GRAIN), (3 * GRAIN, size)])
        self.assertEqual(self.parse(thin_xml(extent(100, 8), 8), size=size), [])
        with self.assertRaisesRegex(ValueError, "count"):
            self.parse(thin_xml(extent(100, 8), 9), size=size)
        with self.assertRaisesRegex(ValueError, "unordered|overlapping"):
            self.parse(thin_xml(single(101) + single(100), 2), size=size)

    def test_missing_wrong_duplicate_and_invalid_device(self):
        empty = thin_xml()
        invalid = [
            empty.replace(b'<device dev_id="731" mapped_blocks="0" transaction="16" '
                          b'creation_time="1" snap_time="2"></device>', b""),
            thin_xml(thin_id=732),
            empty.replace(b' dev_id="731"', b""),
            thin_xml(thin_id=-1),
            thin_xml(thin_id=1 << 24),
            empty.replace(b'</superblock>',
                          b'<device dev_id="731" mapped_blocks="0" transaction="16" '
                          b'creation_time="1" snap_time="2"/></superblock>'),
        ]
        for xml in invalid:
            with self.subTest(xml=xml), self.assertRaises(ValueError):
                self.parse(xml)

    def test_invalid_numeric_values_and_missing_attributes(self):
        valid = thin_xml(single(), 1)
        attributes = (b'uuid=""', b'time="3"', b'transaction="17"',
                      b'nr_data_blocks="1048576"', b'data_block_size="128"',
                      b'dev_id="731"', b'mapped_blocks="1"', b'transaction="16"',
                      b'creation_time="1"', b'snap_time="2"', b'origin_block="1"',
                      b'data_block="91"', b'time="2"')
        for attribute in attributes:
            with self.subTest(missing=attribute), self.assertRaises(ValueError):
                self.parse(valid.replace(b" " + attribute, b"", 1))
        for value in ("-1", "+1", " 1", "1.0", "0x1", "", "x", str(1 << 64)):
            for attribute in (b'origin_block="1"', b'data_block="91"', b'mapped_blocks="1"'):
                field = attribute.split(b"=")[0]
                with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                    self.parse(valid.replace(attribute, field + b'="' + value.encode() + b'"'))
        with self.assertRaisesRegex(ValueError, "data_block_size"):
            self.parse(valid, sectors=256)

    def test_counts_order_overlap_zero_length_and_overflow(self):
        invalid = [
            (single(), 0), (single(), 2), ("", 1),
            (single(2) + single(1), 2), (single(1) + single(1), 2),
            (extent(1, 3) + single(3), 4), (extent(1, 0), 0),
            (extent((1 << 64) - 1, 2), 2),
        ]
        for mappings, count in invalid:
            with self.subTest(mappings=mappings, count=count), self.assertRaises(ValueError):
                self.parse(thin_xml(mappings, count))

    def test_rejects_malformed_truncated_and_unsupported_xml(self):
        valid = thin_xml(single(), 1)
        invalid = [b"", valid[:-1], valid[:len(valid) // 2], b"<superblock>",
                   valid.replace(b"single_mapping", b"mapping"),
                   valid.replace(b"<single_mapping", b"<wrapper><single_mapping")
                   .replace(b"/></device>", b"/></wrapper></device>"),
                   valid.replace(b"/></device>", b"/>unexpected</device>"),
                   valid.replace(b"<superblock", b"<other").replace(b"</superblock>", b"</other>"),
                   valid + valid]
        for xml in invalid:
            with self.subTest(xml=xml), self.assertRaises((ValueError, ET.ParseError)):
                self.parse(xml)

    def test_invalid_parser_arguments(self):
        for thin_id, sectors, size in ((-1, 128, 512), (1 << 24, 128, 512),
                                      (731, 0, 512), (731, -1, 512),
                                      (731, 128, 0), (731, 128, 513)):
            with self.subTest(args=(thin_id, sectors, size)), self.assertRaises(ValueError):
                self.parse(thin_xml(), sectors, size, thin_id)


class DiscoveryTests(unittest.TestCase):
    @contextmanager
    def topology(self, thin="0 4096 thin 253:47 731", pool=None, mode=stat.S_IFBLK,
                 device=None):
        lv = "/dev/research-vg-fast/guest-disk-any-name"
        metadata = Path("/dev/mapper/research--vg--fast-pool--alpha_tmeta")
        pool = pool or "0 2097152 thin-pool 253:61 253:62 256 1024 1 skip_block_zeroing"
        replies = {("dmsetup", "table", lv): thin,
                   ("dmsetup", "table", "-j", "253", "-m", "47"): pool}

        def run(*command, **kwargs):
            self.assertEqual(kwargs, {})
            self.assertIn(command, replies)
            return subprocess.CompletedProcess(command, 0, replies[command], "")

        with ExitStack() as stack:
            commands = stack.enter_context(patch.object(pv, "_run", side_effect=run))
            tools = stack.enter_context(patch.object(pv.shutil, "which", return_value="/mock/tool"))
            resolve = stack.enter_context(patch.object(pv.Path, "resolve", return_value=metadata))
            stack.enter_context(patch.object(pv.Path, "stat", return_value=SimpleNamespace(
                st_mode=mode, st_rdev=os.makedev(253, 61) if device is None else device)))
            reserve = stack.enter_context(patch.object(pv, "_thin_reserved_map",
                                                      return_value=[(0, GRAIN)]))
            yield SimpleNamespace(lv=lv, metadata=metadata, run=commands, tools=tools,
                                  resolve=resolve, reserve=reserve)

    def test_arbitrary_names_and_thin_id_resolve_major_minor(self):
        with self.topology() as state:
            self.assertEqual(pv._thin_map(state.lv, 4096 * 512), [(0, GRAIN)])
            self.assertEqual(state.run.call_args_list, [
                call("dmsetup", "table", state.lv),
                call("dmsetup", "table", "-j", "253", "-m", "47")])
            state.reserve.assert_called_once_with(("-j", "253", "-m", "47"), 2097152,
                                                  str(state.metadata), 731, 256, 4096 * 512)
            state.resolve.assert_called_once_with(strict=True)
            self.assertEqual(state.tools.call_args_list, [call("dmsetup"), call("thin_dump")])

    def test_wrong_thin_target_segments_external_origin_and_capacity(self):
        invalid = ["0 4096 linear 253:47 0", "1 4096 thin 253:47 731", "",
                   "0 2048 thin 253:47 731\n2048 2048 thin 253:47 731",
                   "0 4096 thin 253:47 731 8:9", "0 4096 thin 253:47",
                   "0 4096 thin bad 731", "0 4096 thin 253:47 -1",
                   f"0 4096 thin 253:47 {1 << 24}", "0 2048 thin 253:47 731"]
        for table in invalid:
            with self.subTest(table=table), self.topology(thin=table) as state:
                with self.assertRaisesRegex(RuntimeError, "--no-thin-map"):
                    pv._thin_map(state.lv, 4096 * 512)
                state.reserve.assert_not_called()
                self.assertEqual(state.run.call_count, 1)
        with self.topology(thin=invalid[4]) as state:
            with self.assertRaisesRegex(RuntimeError, "External-origin"):
                pv._thin_map(state.lv, 4096 * 512)

    def test_invalid_pool_and_metadata_device(self):
        invalid = ["0 2097152 linear 253:61 0", "0 2097152 thin-pool 253:61",
                   "0 2097152 thin-pool bad 253:62 128 0",
                   "0 2097152 thin-pool 253:61 bad 128 0",
                   "0 2097152 thin-pool 253:61 253:62 64 0",
                   "0 2097152 thin-pool 253:61 253:62 129 0",
                   "0 2097152 thin-pool 253:61 253:62 2097280 0",
                   "0 2097152 thin-pool 253:61 253:62 128 -1",
                   "0 2097152 thin-pool 253:61 253:62 128 0 2 skip_block_zeroing"]
        for table in invalid:
            with self.subTest(table=table), self.topology(pool=table) as state:
                with self.assertRaisesRegex(RuntimeError, "--no-thin-map"):
                    pv._thin_map(state.lv, 4096 * 512)
                state.reserve.assert_not_called()
        for kwargs in ({"mode": stat.S_IFREG}, {"device": os.makedev(253, 99)}):
            with self.subTest(kwargs=kwargs), self.topology(**kwargs) as state:
                with self.assertRaisesRegex(RuntimeError, "expected block device"):
                    pv._thin_map(state.lv, 4096 * 512)
                state.reserve.assert_not_called()
        with self.topology() as state:
            state.resolve.side_effect = FileNotFoundError("metadata is absent")
            with self.assertRaisesRegex(RuntimeError, "metadata is absent"):
                pv._thin_map(state.lv, 4096 * 512)
            state.reserve.assert_not_called()

    def test_missing_tools_and_command_failure_are_actionable(self):
        for missing in ("dmsetup", "thin_dump"):
            with self.subTest(missing=missing), self.topology() as state:
                state.tools.side_effect = lambda name: None if name == missing else "/mock/tool"
                with self.assertRaisesRegex(RuntimeError, f"{missing}.*--no-thin-map"):
                    pv._thin_map(state.lv, 4096 * 512)
                state.run.assert_not_called()
                state.reserve.assert_not_called()
        with self.topology() as state:
            state.run.side_effect = subprocess.CalledProcessError(1, "dmsetup", stderr="permission denied")
            with self.assertRaisesRegex(RuntimeError, "permission denied.*--no-thin-map"):
                pv._thin_map(state.lv, 4096 * 512)
            state.reserve.assert_not_called()

    def test_source_size_uses_run_and_rejects_invalid_sizes(self):
        with patch.object(pv, "_run", return_value=SimpleNamespace(stdout=" 2097664\n")) as run:
            self.assertEqual(pv._source_size("/mock/lv"), 2097664)
            run.assert_called_once_with("blockdev", "--getsize64", "/mock/lv")
        for value in ("", "0", "-512", "513", "1.5", "invalid"):
            with self.subTest(value=value), patch.object(pv, "_run", return_value=SimpleNamespace(stdout=value)):
                with self.assertRaisesRegex(RuntimeError, "Cannot size.*blockdev"):
                    pv._source_size("/mock/lv")
        for error in (FileNotFoundError("blockdev"),
                      subprocess.CalledProcessError(1, "blockdev", stderr=b"not active")):
            with self.subTest(error=error), patch.object(pv, "_run", side_effect=error):
                with self.assertRaisesRegex(RuntimeError, "ensure the LV is active"):
                    pv._source_size("/mock/lv")

    def test_arbitrary_storage_config_and_non_thin_rejection(self):
        config = """name: arbitrary-guest
cores: 2
sockets: 2
scsi0: research-fast:guest-disk-alpha,size=2G
virtio1: file=archive-beta:disk-with-hyphens,size=1G
ide2: optical:installer.iso,media=cdrom
net0: virtio=00:11:22:33:44:55,bridge=bridge-west
"""
        with patch.object(pv.Path, "exists", return_value=True), \
                patch.object(pv.Path, "read_text", return_value=config):
            result = pv._vm_config(880)
        self.assertEqual(result["disks"], ["research-fast:guest-disk-alpha",
                                           "archive-beta:disk-with-hyphens"])
        self.assertEqual(result["vcpus"], 4)
        storage = "lvmthin: research-fast\n\tvgname research-vg\nlvmthin: archive-beta\n"
        with patch.object(pv.Path, "read_text", return_value=storage):
            pv._check_disk_storages(result["disks"])
        for storage_type in ("lvm", "dir", "zfspool"):
            with self.subTest(storage_type=storage_type), patch.object(
                    pv.Path, "read_text", return_value=f"{storage_type}: research-fast\n"):
                with self.assertRaisesRegex(SystemExit, "must be lvmthin"):
                    pv._check_disk_storages(result["disks"][:1])


class ThinDumpReaderTests(unittest.TestCase):
    def test_polls_until_readable_and_returns_short_reads_and_eof(self):
        stream = Mock(spec=io.FileIO)
        stream.read.side_effect = [b"partial", b""]
        check = Mock()
        events = Mock()
        events.attach_mock(check, "check")
        events.attach_mock(stream.read, "read")
        with patch.object(pv.select, "select", side_effect=[
                ([], [], []), ([], [], []), ([stream], [], []), ([stream], [], [])]) as poll:
            events.attach_mock(poll, "poll")
            reader = pv._ThinDumpReader(stream, check)
            self.assertEqual(reader.read(16384), b"partial")
            self.assertEqual(reader.read(16384), b"")
        polling = [call.check(), call.poll([stream], [], [], 0.1)]
        self.assertEqual(events.mock_calls,
                         polling * 3 + [call.read(16384)] + polling + [call.read(16384)])

    def test_pending_termination_interrupts_before_poll_or_read(self):
        for sig in (signal.SIGINT, signal.SIGTERM):
            originals = {s: signal.getsignal(s) for s in (signal.SIGINT, signal.SIGTERM)}
            stream = Mock(spec=io.FileIO)
            with self.subTest(signal=sig), patch.object(pv.select, "select") as poll:
                try:
                    with self.assertRaises(SystemExit) as raised:
                        with pv._deferred_termination() as check:
                            signal.getsignal(sig)(sig, None)
                            pv._ThinDumpReader(stream, check).read(16384)
                    self.assertEqual(str(raised.exception), f"Interrupted (signal {sig})")
                    poll.assert_not_called()
                    stream.read.assert_not_called()
                    self.assertEqual({s: signal.getsignal(s) for s in originals}, originals)
                finally:
                    for s, handler in originals.items():
                        signal.signal(s, handler)


class ReservationTests(unittest.TestCase):
    pool = ("-j", "253", "-m", "47")
    pid = 54321

    @contextmanager
    def reservation(self, xml=None, roots=(None, 42), status=0, stderr=b"",
                    reserve_error=None, release_error=None, spawn_error=None,
                    parse_error=None, restore_interrupt=None):
        state = SimpleNamespace(events=[], fds=[], mask=set(), restores=0,
                                handlers={sig: signal.getsignal(sig)
                                          for sig in (signal.SIGINT, signal.SIGTERM)})
        xml = thin_xml(single(), 1) if xml is None else xml

        def run(*command):
            self.assertEqual(command[:-1], ("dmsetup", "message", *self.pool, "0"))
            operation = command[-1]
            self.assertIn(operation, ("reserve_metadata_snap", "release_metadata_snap"))
            self.assertEqual(state.mask, {signal.SIGINT, signal.SIGTERM})
            state.events.append(operation)
            error = reserve_error if operation == "reserve_metadata_snap" else release_error
            if error is not None:
                raise error
            return subprocess.CompletedProcess(command, 0, "", "")

        def sigmask(how, mask):
            previous = state.mask.copy()
            if how == signal.SIG_BLOCK:
                state.mask |= set(mask)
            else:
                self.assertEqual(how, signal.SIG_SETMASK)
                state.mask = set(mask)
                state.restores += 1
                if state.restores == restore_interrupt:
                    raise KeyboardInterrupt("signal delivered on mask restoration")
            return previous

        def spawn(command, argv, environ, *, file_actions, setsigmask, setsigdef):
            state.events.append("spawn")
            self.assertEqual(state.mask, {signal.SIGINT, signal.SIGTERM})
            self.assertEqual(command, "thin_dump")
            self.assertEqual(argv, ["thin_dump", "--format", "xml", "--dev-id", "731",
                                    "--metadata-snap=42", "/mock/metadata"])
            self.assertIs(environ, os.environ)
            self.assertEqual(setsigmask, set())
            self.assertEqual(setsigdef, (signal.SIGPIPE,))
            self.assertEqual([action[0] for action in file_actions],
                             [os.POSIX_SPAWN_DUP2, os.POSIX_SPAWN_DUP2,
                              os.POSIX_SPAWN_CLOSE, os.POSIX_SPAWN_CLOSE])
            write_fd = file_actions[0][1]
            error_fd = file_actions[1][1]
            read_fd = file_actions[2][1]
            self.assertEqual(file_actions[0][2], 1)
            self.assertEqual(file_actions[1][2], 2)
            self.assertEqual(file_actions[3][1], write_fd)
            state.fds.extend((read_fd, write_fd))
            if spawn_error is not None:
                raise spawn_error
            os.write(write_fd, xml)
            os.write(error_fd, stderr)
            return self.pid

        def waitpid(pid, options):
            self.assertEqual(pid, self.pid)
            state.events.append("reap")
            return pid, status

        with ExitStack() as stack:
            for sig, handler in state.handlers.items():
                stack.callback(signal.signal, sig, handler)
            state.run = stack.enter_context(patch.object(pv, "_run", side_effect=run))
            state.roots = stack.enter_context(patch.object(pv, "_thin_held_root", side_effect=roots))
            state.spawn = stack.enter_context(patch.object(pv.os, "posix_spawnp", side_effect=spawn))
            state.wait = stack.enter_context(patch.object(pv.os, "waitpid", side_effect=waitpid))
            state.kill = stack.enter_context(patch.object(pv.os, "kill"))
            state.signals = stack.enter_context(patch.object(pv.signal, "pthread_sigmask", side_effect=sigmask))
            state.log = stack.enter_context(patch.object(pv, "log"))
            if parse_error is not None:
                stack.enter_context(patch.object(pv, "_parse_thin_dump", side_effect=parse_error))
            try:
                yield state
            finally:
                self.assertEqual(state.mask, set())
                self.assertEqual({sig: signal.getsignal(sig) for sig in state.handlers}, state.handlers)
                for fd in state.fds:
                    with self.assertRaises(OSError):
                        os.fstat(fd)

    def capture(self):
        return pv._thin_reserved_map(self.pool, 2097152, "/mock/metadata", 731, 128, 4 * GRAIN)

    def test_reserve_dump_reap_then_release(self):
        with self.reservation() as state:
            self.assertEqual(self.capture(), [(GRAIN, 2 * GRAIN)])
            self.assertEqual(state.events, ["reserve_metadata_snap", "spawn", "reap",
                                            "release_metadata_snap"])
            self.assertEqual(state.roots.call_args_list, [call(self.pool, 2097152)] * 2)
            state.wait.assert_called_once_with(self.pid, os.WNOHANG)
            state.kill.assert_not_called()

    def test_existing_reservation_and_failed_reserve_are_never_released(self):
        with self.reservation(roots=(99,)) as state:
            with self.assertRaisesRegex(RuntimeError, "already has a metadata reservation"):
                self.capture()
            state.run.assert_not_called()
            state.spawn.assert_not_called()
        for error in (subprocess.CalledProcessError(1, "reserve", stderr="already held"),
                      KeyboardInterrupt(), SystemExit("interrupted")):
            with self.subTest(error=type(error)), self.reservation(reserve_error=error) as state:
                expected = RuntimeError if isinstance(error, Exception) else type(error)
                with self.assertRaises(expected):
                    self.capture()
                self.assertEqual(state.events, ["reserve_metadata_snap"])
                state.spawn.assert_not_called()

    def test_missing_reserved_root_and_failed_spawn_release_owned_snapshot(self):
        with self.reservation(roots=(None, None)) as state:
            with self.assertRaisesRegex(RuntimeError, "did not expose"):
                self.capture()
            self.assertEqual(state.events, ["reserve_metadata_snap", "release_metadata_snap"])
        with self.reservation(spawn_error=FileNotFoundError("thin_dump absent")) as state:
            with self.assertRaisesRegex(RuntimeError, "thin_dump absent"):
                self.capture()
            self.assertEqual(state.events, ["reserve_metadata_snap", "spawn", "release_metadata_snap"])
            state.wait.assert_not_called()

    def test_dump_failure_and_stderr_tail(self):
        for status, expected in ((7 << 8, "status 7"), (signal.SIGTERM, "status -15")):
            with self.subTest(status=status), self.reservation(
                    status=status, stderr=b"x" * 6000 + b"metadata read failed") as state:
                with self.assertRaisesRegex(RuntimeError, expected) as raised:
                    self.capture()
                self.assertIn("metadata read failed", str(raised.exception))
                self.assertLess(len(str(raised.exception)), 4500)
                self.assertEqual(state.events[-2:], ["reap", "release_metadata_snap"])

    def test_invalid_xml_and_parser_interrupts_reap_before_release(self):
        for kwargs, expected in (({"xml": b"<broken>"}, RuntimeError),
                                 ({"parse_error": OSError("I/O failure")}, RuntimeError),
                                 ({"parse_error": KeyboardInterrupt()}, KeyboardInterrupt),
                                 ({"parse_error": SystemExit("SIGTERM")}, SystemExit)):
            with self.subTest(kwargs=kwargs), self.reservation(**kwargs) as state:
                with self.assertRaises(expected):
                    self.capture()
                self.assertEqual(state.events[-2:], ["reap", "release_metadata_snap"])
                state.wait.assert_called_once_with(self.pid, os.WNOHANG)

    def test_interrupt_on_unmask_preserves_ownership_and_spawn_pid(self):
        for restore in (1, 2):
            with self.subTest(restore=restore), self.reservation(restore_interrupt=restore) as state:
                with self.assertRaises(KeyboardInterrupt):
                    self.capture()
                self.assertEqual(state.events[-1], "release_metadata_snap")
                self.assertEqual(state.events.count("release_metadata_snap"), 1)
                if restore == 2:
                    self.assertEqual(state.events[-2], "reap")
                else:
                    state.spawn.assert_not_called()

    def test_real_handler_at_cleanup_entry_defers_until_release(self):
        source, start = inspect.getsourcelines(pv._thin_reserved_map)
        cleanup_line, = (start + i for i, line in enumerate(source)
                         if line.strip() == "original_error = sys.exc_info()[1]")
        release_line, = (start + i for i, line in enumerate(source)
                         if '"release_metadata_snap")' in line)
        for sig in (signal.SIGINT, signal.SIGTERM):
            for repeat in (False, True):
                with self.subTest(signal=sig, repeat=repeat), self.reservation() as state:
                    delivered = []

                    def trace(frame, event, arg):
                        if frame.f_code is pv._thin_reserved_map.__code__ and event == "line":
                            if frame.f_lineno == cleanup_line:
                                self.assertEqual(state.mask, set())
                                delivered.append(sig)
                                state.events.append("cleanup interrupt")
                            elif repeat and frame.f_lineno == release_line:
                                self.assertEqual(state.mask, {signal.SIGINT, signal.SIGTERM})
                                delivered.append(signal.SIGTERM if sig == signal.SIGINT else signal.SIGINT)
                                state.events.append("teardown interrupt")
                            else:
                                return trace
                            self.assertNotIn("release_metadata_snap", state.events)
                            handler = signal.getsignal(delivered[-1])
                            self.assertTrue(callable(handler))
                            self.assertIsNot(handler, state.handlers[delivered[-1]])
                            handler(delivered[-1], frame)
                        return trace

                    previous_trace = sys.gettrace()
                    try:
                        sys.settrace(trace)
                        with self.assertRaises(SystemExit) as raised:
                            self.capture()
                    finally:
                        sys.settrace(previous_trace)
                    self.assertEqual(str(raised.exception), f"Interrupted (signal {sig})")
                    self.assertEqual(len(delivered), 2 if repeat else 1)
                    expected = ["reserve_metadata_snap", "spawn", "reap", "cleanup interrupt"]
                    if repeat:
                        expected.append("teardown interrupt")
                    self.assertEqual(state.events, expected + ["release_metadata_snap"])
                    state.wait.assert_called_once_with(self.pid, os.WNOHANG)

    def test_stalled_dump_read_checks_pending_termination(self):
        for sig in (signal.SIGINT, signal.SIGTERM):
            with self.subTest(signal=sig), self.reservation() as state, \
                    patch.object(pv.select, "select") as poll, \
                    patch.object(pv.os, "fdopen", wraps=os.fdopen) as fdopen:
                def timeout(readers, writers, errors, delay):
                    self.assertEqual(poll.call_count, 1)
                    self.assertEqual((writers, errors, delay), ([], [], 0.1))
                    self.assertEqual(len(readers), 1)
                    self.assertIsInstance(readers[0], io.FileIO)
                    self.assertEqual(state.mask, set())
                    state.events.append("read timeout")
                    signal.getsignal(sig)(sig, None)
                    return [], [], []

                poll.side_effect = timeout
                with self.assertRaises(SystemExit) as raised:
                    self.capture()
                self.assertEqual(str(raised.exception), f"Interrupted (signal {sig})")
                fdopen.assert_called_once_with(state.fds[0], "rb", buffering=0)
                self.assertEqual(poll.call_count, 1)
                self.assertEqual(state.events, ["reserve_metadata_snap", "spawn", "read timeout",
                                                "reap", "release_metadata_snap"])
                state.wait.assert_called_once_with(self.pid, os.WNOHANG)

    def test_stalled_dump_wait_checks_pending_termination(self):
        for sig in (signal.SIGINT, signal.SIGTERM):
            with self.subTest(signal=sig), self.reservation() as state, \
                    patch.object(pv.time, "sleep") as sleep:
                def waitpid(pid, options):
                    self.assertEqual((pid, options), (self.pid, os.WNOHANG))
                    if state.wait.call_count == 1:
                        state.events.append("wait pending")
                        return 0, 0
                    self.assertEqual(state.wait.call_count, 2)
                    self.assertEqual(state.mask, {signal.SIGINT, signal.SIGTERM})
                    state.events.append("reap")
                    return pid, 0

                def interrupt(delay):
                    self.assertEqual(delay, 0.05)
                    self.assertEqual(state.mask, set())
                    state.events.append("wait interrupt")
                    signal.getsignal(sig)(sig, None)

                state.wait.side_effect = waitpid
                sleep.side_effect = interrupt
                with self.assertRaises(SystemExit) as raised:
                    self.capture()
                self.assertEqual(str(raised.exception), f"Interrupted (signal {sig})")
                self.assertEqual(state.wait.call_args_list, [call(self.pid, os.WNOHANG)] * 2)
                sleep.assert_called_once_with(0.05)
                self.assertEqual(state.events, ["reserve_metadata_snap", "spawn", "wait pending",
                                                "wait interrupt", "reap", "release_metadata_snap"])

    def test_deferral_startup_errors_restore_actual_signal_handlers(self):
        install = signal.signal
        for stage in (signal.SIGINT, signal.SIGTERM, "temporary file"):
            with self.subTest(stage=stage), self.reservation() as state, ExitStack() as stack:
                def install_handler(sig, handler):
                    if sig == stage:
                        if sig == signal.SIGTERM:
                            self.assertIsNot(signal.getsignal(signal.SIGINT), state.handlers[signal.SIGINT])
                        raise OSError("handler setup failed")
                    return install(sig, handler)

                def temporary_file():
                    for sig, handler in state.handlers.items():
                        self.assertIsNot(signal.getsignal(sig), handler)
                    raise OSError("temporary file setup failed")

                if stage == "temporary file":
                    stack.enter_context(patch.object(pv.tempfile, "TemporaryFile", side_effect=temporary_file))
                else:
                    stack.enter_context(patch.object(pv.signal, "signal", side_effect=install_handler))
                with self.assertRaisesRegex(OSError, "setup failed"):
                    self.capture()
                self.assertEqual({sig: signal.getsignal(sig) for sig in state.handlers}, state.handlers)
                state.run.assert_not_called()
                state.spawn.assert_not_called()
                state.wait.assert_not_called()

    def test_status_timeout_or_pending_signal_releases_before_spawning(self):
        with self.reservation(roots=(None, subprocess.TimeoutExpired("dmsetup status", 30))) as state:
            with self.assertRaisesRegex(RuntimeError, "timed out"):
                self.capture()
            self.assertEqual(state.events, ["reserve_metadata_snap", "release_metadata_snap"])
            state.spawn.assert_not_called()
        with self.reservation() as state:
            def status(*args):
                if state.roots.call_count == 1:
                    return None
                signal.getsignal(signal.SIGTERM)(signal.SIGTERM, None)
                return 42
            state.roots.side_effect = status
            with self.assertRaisesRegex(SystemExit, "Interrupted"):
                self.capture()
            self.assertEqual(state.events, ["reserve_metadata_snap", "release_metadata_snap"])
            state.spawn.assert_not_called()
        with patch.object(pv.subprocess, "run", side_effect=subprocess.TimeoutExpired("dmsetup status", 30)) as run:
            with self.assertRaises(subprocess.TimeoutExpired):
                pv._thin_held_root(self.pool, 2097152)
            run.assert_called_once_with(["dmsetup", "status", *self.pool], check=True,
                                        capture_output=True, text=True, timeout=30)

    def test_handler_restoration_blocks_both_termination_signals(self):
        install = signal.signal
        with self.reservation() as state:
            restored = []

            def restore(sig, handler):
                if handler is state.handlers[sig]:
                    self.assertEqual(state.mask, {signal.SIGINT, signal.SIGTERM})
                    restored.append(sig)
                return install(sig, handler)

            with patch.object(pv.signal, "signal", side_effect=restore):
                self.capture()
            self.assertEqual(restored, [signal.SIGINT, signal.SIGTERM])

    def test_release_failure_reports_manual_recovery(self):
        error = subprocess.CalledProcessError(1, "release", stderr="busy")
        with self.reservation(release_error=error):
            with self.assertRaisesRegex(RuntimeError, "Cannot release our metadata reservation") as raised:
                self.capture()
            message = str(raised.exception)
            for text in ("253:47", "/mock/metadata", "release_metadata_snap", "busy", "reader remains"):
                self.assertIn(text, message)

    def test_cleanup_failure_retains_reservation_and_original_error(self):
        original = ValueError("original parsing failure")
        with self.reservation(parse_error=original) as state, \
                patch.object(pv, "_stop_thin_dump", side_effect=OSError("cannot reap")):
            with self.assertRaisesRegex(RuntimeError, "original parsing failure") as raised:
                self.capture()
            self.assertIs(raised.exception.__cause__, original)
            self.assertNotIn("release_metadata_snap", state.events)
            self.assertIn("reservation retained", str(state.log.error.call_args))
        for original in (ValueError("original failure"), KeyboardInterrupt()):
            with self.subTest(original=type(original)), self.reservation(
                    parse_error=original, release_error=OSError("release failure")) as state:
                expected = RuntimeError if isinstance(original, Exception) else KeyboardInterrupt
                with self.assertRaises(expected):
                    self.capture()
                state.log.error.assert_called_once()
                self.assertEqual(state.events[-2:], ["reap", "release_metadata_snap"])

    def test_pool_status_root_and_validation(self):
        prefix = "0 2097152 thin-pool 17 10/100 20/200 "
        for root in ("-", "42"):
            with self.subTest(root=root), patch.object(
                    pv, "_run", return_value=SimpleNamespace(stdout=prefix + root + " rw discard_passdown queue_if_no_space -")):
                self.assertEqual(pv._thin_held_root(self.pool, 2097152), None if root == "-" else 42)
        invalid = [prefix + "0 rw discard_passdown queue_if_no_space -",
                   prefix + "42 Fail discard_passdown queue_if_no_space -",
                   prefix + "42 rw discard_passdown queue_if_no_space needs_check",
                   prefix.replace("10/100", "101/100") + "- rw discard_passdown queue_if_no_space -",
                   prefix.replace("10/100", "10") + "- rw discard_passdown queue_if_no_space -",
                   prefix.replace("2097152", "2097153") + "- rw discard_passdown queue_if_no_space -"]
        for text in invalid:
            with self.subTest(status=text), patch.object(pv, "_run", return_value=SimpleNamespace(stdout=text)):
                with self.assertRaises(ValueError):
                    pv._thin_held_root(self.pool, 2097152)

    def test_stop_dump_terminates_and_escalates_before_reaping(self):
        with patch.object(pv.os, "waitpid", side_effect=[(0, 0), (self.pid, 0)]) as wait, \
                patch.object(pv.os, "kill") as kill:
            pv._stop_thin_dump(self.pid)
            kill.assert_called_once_with(self.pid, signal.SIGTERM)
            self.assertEqual(wait.call_args_list, [call(self.pid, os.WNOHANG)] * 2)
        with patch.object(pv.os, "waitpid", side_effect=[(0, 0), (0, 0), (self.pid, 0)]) as wait, \
                patch.object(pv.os, "kill") as kill, \
                patch.object(pv.time, "monotonic", side_effect=[0, 0, 6]), \
                patch.object(pv.time, "sleep"):
            pv._stop_thin_dump(self.pid)
            self.assertEqual(kill.call_args_list, [call(self.pid, signal.SIGTERM), call(self.pid, signal.SIGKILL)])
            self.assertEqual(wait.call_args_list[-1], call(self.pid, 0))
        with patch.object(pv.os, "waitpid", side_effect=ChildProcessError), \
                patch.object(pv.os, "kill") as kill:
            pv._stop_thin_dump(self.pid)
            kill.assert_not_called()


class VmdkTests(TemporaryTestCase):
    def convert(self, size, pieces, ranges, name="disk", workers=2, short=None):
        source = self.source(size, pieces, name + ".raw")
        destination = self.directory / (name + ".vmdk")
        reads, returned, batches, compressed, progress = [], [], [], [], []
        real_pread, real_batch, real_compress = os.pread, pv._compress_batch, zlib.compress
        allowed = [(0, size)] if ranges is None else ranges

        def pread(fd, length, offset):
            self.assertGreater(length, 0)
            self.assertTrue(any(lo <= offset < offset + length <= hi for lo, hi in allowed),
                            f"read intersects an unmapped byte: {offset}+{length}, allowed={allowed}")
            reads.append((offset, length))
            data = real_pread(fd, length if short is None else min(short, length), offset)
            returned.append(len(data))
            return data

        def compress_batch(raw, level, mask=None):
            batches.append((len(raw) // GRAIN, None if mask is None else bytes(mask)))
            return real_batch(raw, level, mask)

        def compress(raw, **kwargs):
            compressed.append(len(raw))
            return real_compress(raw, **kwargs)

        with patch.object(pv, "_source_size", return_value=size) as sizing, \
                patch.object(pv.os, "pread", side_effect=pread), \
                patch.object(pv, "_compress_batch", side_effect=compress_batch), \
                patch.object(pv.zlib, "compress", side_effect=compress):
            digest = pv.VmdkWriter(str(source), destination, workers, level=1,
                                   mapped_ranges=ranges, src_size=size,
                                   on_progress=lambda done, total: progress.append((done, total))).convert()
        sizing.assert_called_once_with(str(source))
        data = destination.read_bytes()
        self.assertEqual(digest, hashlib.sha256(data).hexdigest())
        target = sum(hi - lo for lo, hi in allowed)
        expected_progress = []
        for end in range(pv.BATCH_GRAINS * GRAIN, size + pv.BATCH_GRAINS * GRAIN,
                         pv.BATCH_GRAINS * GRAIN):
            done = sum(max(0, min(hi, end) - lo) for lo, hi in allowed)
            if done < target:
                expected_progress.append((done, target))
        self.assertEqual(progress, expected_progress + [(target, target)])
        self.assertEqual(sum(returned), sum(hi - lo for lo, hi in allowed))
        if short is None:
            self.assertEqual(sum(length for _, length in reads), sum(returned))
        decoded = decode_vmdk(self, data, size)
        assert_logical_contents(self, decoded, size, pieces)
        self.assertEqual(len(compressed), len(decoded.grains))
        return SimpleNamespace(source=source, destination=destination, data=data, decoded=decoded,
                               reads=reads, batches=batches, compressed=compressed, digest=digest,
                               progress=progress)


    def test_fully_allocated_empty_and_mapped_zero_devices(self):
        size = 2 * GRAIN + 512
        pieces = [(0, b"A" * GRAIN), (GRAIN, b"B" * GRAIN), (2 * GRAIN, b"C" * 512)]
        self.convert(size, pieces, [(0, size)], "allocated")
        for name, ranges in (("empty", []), ("mapped-zero", [(0, size)]), ("full-read-zero", None)):
            with self.subTest(name=name):
                result = self.convert(size, [], ranges, name)
                self.assertEqual(result.decoded.grains, {})
                self.assertEqual(result.compressed, [])
                if ranges == []:
                    self.assertEqual(result.reads, [])
                    self.assertEqual(result.batches, [])
                else:
                    self.assertEqual(result.reads, [(0, size)])
                    self.assertEqual(len(result.batches), 1)

    def test_progress_counts_source_reads_including_zero_data_not_holes_or_padding(self):
        size = 9 * GRAIN + 512
        pieces = [(0, b"A" * 512), (8 * GRAIN, b"B" * 512)]
        ranges = [(0, 512), (3 * GRAIN, 3 * GRAIN + 1024), (8 * GRAIN, 8 * GRAIN + 512)]
        with patch.object(pv, "BATCH_GRAINS", 2):
            sparse = self.convert(size, pieces, ranges, "progress-sparse")
            dense = self.convert(size, pieces, None, "progress-dense")
            empty = self.convert(size, [], [], "progress-empty")
        self.assertEqual(sparse.progress, [(512, 2048), (1536, 2048), (1536, 2048),
                                           (1536, 2048), (2048, 2048)])
        self.assertEqual(dense.progress, [(2 * GRAIN, size), (4 * GRAIN, size),
                                          (6 * GRAIN, size), (8 * GRAIN, size), (size, size)])
        self.assertEqual(empty.progress, [(0, 0)])

    def test_subgrain_holes_and_fragmented_ranges(self):
        size = 3 * GRAIN + 512
        pieces = [(512, b"A" * 1024), (4096, b"B" * 512),
                  (GRAIN - 512, b"C" * 1024), (2 * GRAIN + 4096, b"D" * 512),
                  (3 * GRAIN, b"E" * 512)]
        ranges = [(offset, offset + len(data)) for offset, data in pieces]
        ranges.insert(3, (GRAIN + 4096, GRAIN + 4608))
        result = self.convert(size, pieces, ranges)
        self.assertEqual(result.reads, [(lo, hi - lo) for lo, hi in ranges])
        self.assertEqual(result.batches, [(4, b"\x01" * 4)])

    def test_batch_and_table_boundaries(self):
        for count in (255, 256, 257, 511, 512, 513):
            with self.subTest(grains=count):
                size = (count - 1) * GRAIN + 512
                selected = sorted({0, count - 1, *[i for i in (254, 255, 256, 510, 511, 512) if i < count]})
                pieces = [(grain * GRAIN, bytes([grain % 251 + 1]) * 512) for grain in selected]
                ranges = [(offset, offset + len(data)) for offset, data in pieces]
                result = self.convert(size, pieces, ranges, f"boundary-{count}")
                self.assertEqual(result.decoded.lbas, [grain * 128 for grain in selected])
                self.assertEqual(len(result.decoded.tables), (count + 511) // 512)
                self.assertEqual(len(result.batches), (count + 255) // 256)

    def test_one_range_crosses_batch_and_table_boundaries(self):
        size = 514 * GRAIN
        pieces = [(0, b"Z" * 512), (256 * GRAIN - 512, b"A" * 1024),
                  (512 * GRAIN - 512, b"B" * 1024)]
        ranges = [(0, 512), (256 * GRAIN - 512, 512 * GRAIN + 512)]
        result = self.convert(size, pieces, ranges)
        self.assertEqual(result.reads, [(0, 512), (256 * GRAIN - 512, 512),
                                        (256 * GRAIN, 256 * GRAIN), (512 * GRAIN, 512)])
        self.assertEqual(result.batches, [(256, b"\x01" + bytes(254) + b"\x01"),
                                         (256, b"\x01" * 256), (2, b"\x01\x00")])
        self.assertEqual(result.decoded.lbas, [grain * 128 for grain in (0, 255, 256, 511, 512)])

    def test_holes_spanning_batches_and_multiple_tables(self):
        size = 2049 * GRAIN + 512
        pieces = [(0, b"A" * 512), (2049 * GRAIN, b"Z" * 512)]
        ranges = [(offset, offset + len(data)) for offset, data in pieces]
        result = self.convert(size, pieces, ranges)
        self.assertEqual(len(result.decoded.tables), 5)
        for table in result.decoded.tables[1:4]:
            self.assertEqual(table, (0,) * 512)
        self.assertEqual(len(result.batches), 2)
        self.assertEqual(sum(sum(mask) for _, mask in result.batches), 2)
        empty = self.convert(size, [], [], "all-empty")
        self.assertEqual(empty.batches, [])
        self.assertEqual(empty.reads, [])
        self.assertEqual(empty.compressed, [])
        self.assertEqual(empty.decoded.tables, [(0,) * 512] * 5)

    def test_unmapped_grains_skip_compression_even_with_nonzero_input(self):
        raw = b"A" * GRAIN + b"B" * GRAIN + b"C" * GRAIN
        compress = zlib.compress
        with patch.object(pv.zlib, "compress", wraps=compress) as spy:
            result = pv._compress_batch(raw, 6, bytearray([0, 1, 0]))
        self.assertIsNone(result[0])
        self.assertIsNone(result[2])
        self.assertEqual(zlib.decompress(result[1]), b"B" * GRAIN)
        spy.assert_called_once_with(b"B" * GRAIN, level=6)
        with patch.object(pv.zlib, "compress") as spy:
            self.assertEqual(pv._compress_batch(raw, 6, bytearray(3)), [None] * 3)
            self.assertEqual(pv._compress_batch(bytes(GRAIN), 6), [None])
            spy.assert_not_called()

    def test_sparse_and_full_maps_equal_dense_reference_and_retain_zero_omission(self):
        size = 6 * GRAIN + 512
        pieces = [(512, b"A" * 512), (2 * GRAIN, b"B" * GRAIN), (6 * GRAIN, b"C" * 512)]
        ranges = [(offset, offset + len(data)) for offset, data in pieces]
        sparse = self.convert(size, pieces, ranges, "sparse")
        full_map = self.convert(size, pieces, [(0, size)], "full-map")
        dense = self.convert(size, pieces, None, "dense")
        self.assertEqual(sparse.decoded.grains, dense.decoded.grains)
        self.assertEqual(full_map.decoded.grains, dense.decoded.grains)
        self.assertEqual(dense.reads, [(0, size)])
        self.assertEqual(dense.batches, [(7, None)])
        self.assertEqual(dense.decoded.tables[0][1], 0)
        self.assertEqual(dense.decoded.tables[0][3:6], (0, 0, 0))
        for result in (sparse, full_map):
            self.assertEqual(result.data[128 * 512:], dense.data[128 * 512:])
        decoded = bytearray(size)
        for grain, raw in dense.decoded.grains.items():
            start = grain * GRAIN
            decoded[start:min(start + GRAIN, size)] = raw[:min(GRAIN, size - start)]
        self.assertEqual(bytes(decoded), dense.source.read_bytes())

    def test_short_reads_retry_at_correct_offsets(self):
        size = GRAIN + 512
        pieces = [(512, b"A" * 1536), (GRAIN, b"B" * 512)]
        result = self.convert(size, pieces, [(512, 2048), (GRAIN, size)], short=137)
        self.assertEqual(result.reads[:3], [(512, 1536), (649, 1399), (786, 1262)])
        self.convert(size, pieces, None, name="full-short", short=137)
        with patch.object(pv.os, "pread", side_effect=[b"ab", b"c", b"de"]) as pread:
            self.assertEqual(pv._pread_exact(99, 5, 100), b"abcde")
            self.assertEqual(pread.call_args_list, [call(99, 5, 100), call(99, 3, 102), call(99, 2, 103)])

    def test_premature_eof_and_io_errors_abort_and_close_source(self):
        source = self.source(GRAIN)
        real_close = os.close
        for responses, expected in (([b""], EOFError), ([b"abc", b""], EOFError),
                                    ([OSError("read failed")], OSError)):
            with self.subTest(responses=responses), \
                    patch.object(pv, "_source_size", return_value=GRAIN), \
                    patch.object(pv.os, "pread", side_effect=responses), \
                    patch.object(pv.os, "close", wraps=real_close) as close:
                with self.assertRaises(expected):
                    pv.VmdkWriter(str(source), self.directory / "failed.vmdk", 1,
                                  mapped_ranges=[(0, GRAIN)], src_size=GRAIN).convert()
                close.assert_called_once()
                with self.assertRaises(OSError):
                    os.fstat(close.call_args.args[0])

    def test_capacity_rechecked_and_bad_ranges_fail_before_open(self):
        for ranges in ([(-1, 512)], [(0, 0)], [(0, GRAIN + 512)],
                       [(512, 1024), (0, 512)], [(0, 1024), (512, 1536)]):
            with self.subTest(ranges=ranges), patch.object(pv, "_source_size", return_value=GRAIN), \
                    patch.object(pv.os, "open") as opening:
                with self.assertRaisesRegex(ValueError, "Mapped ranges"):
                    pv.VmdkWriter("/mock/source", self.directory / "bad.vmdk", 1,
                                  mapped_ranges=ranges, src_size=GRAIN).convert()
                opening.assert_not_called()
        with patch.object(pv, "_source_size", return_value=GRAIN + 512) as sizing, \
                patch.object(pv.os, "open") as opening:
            with self.assertRaisesRegex(RuntimeError, "capacity changed"):
                pv.VmdkWriter("/mock/source", self.directory / "bad.vmdk", 1,
                              mapped_ranges=[], src_size=GRAIN).convert()
            sizing.assert_called_once_with("/mock/source")
            opening.assert_not_called()
        with self.assertRaisesRegex(ValueError, "workers"):
            pv.VmdkWriter("/mock/source", self.directory / "bad.vmdk", 0)

    def test_pending_compression_is_bounded(self):
        state = SimpleNamespace(outstanding=0, maximum=0, submitted=0, consumed=0)

        class Deferred:
            def __init__(self, function, args):
                self.function, self.args = function, args

            def result(self):
                try:
                    return self.function(*self.args)
                finally:
                    self.args = None
                    state.outstanding -= 1
                    state.consumed += 1

        class Executor:
            def __init__(self, max_workers):
                state.workers = max_workers

            def __enter__(self):
                return self

            def __exit__(self, *args):
                return False

            def submit(self, function, *args):
                state.outstanding += 1
                state.submitted += 1
                state.maximum = max(state.maximum, state.outstanding)
                return Deferred(function, args)

        size = 35 * GRAIN
        pieces = [(grain * GRAIN, b"A" * 512) for grain in range(0, 35, 2)]
        with patch.object(pv, "BATCH_GRAINS", 2), patch.object(pv, "ThreadPoolExecutor", Executor):
            self.convert(size, pieces, [(0, size)], workers=2)
        self.assertEqual(state.workers, 2)
        self.assertEqual(state.submitted, 18)
        self.assertEqual(state.submitted, state.consumed)
        self.assertEqual(state.outstanding, 0)
        self.assertLessEqual(state.maximum, 2 * state.workers + 1)
        self.assertLess(state.maximum, state.submitted)

    @unittest.skipUnless(QEMU_IMG, "qemu-img is not installed")
    def test_qemu_check_and_compare_synthetic_images(self):
        size = 513 * GRAIN + 512
        pieces = [(512, b"A" * 512), (255 * GRAIN, b"B" * 512),
                  (512 * GRAIN, b"C" * GRAIN), (513 * GRAIN, b"D" * 512)]
        ranges = [(offset, offset + len(data)) for offset, data in pieces]
        sparse = self.convert(size, pieces, ranges, "qemu-sparse")
        dense = self.convert(size, pieces, None, "qemu-dense")
        empty = self.convert(size, [], [], "qemu-empty")
        for result in (sparse, dense, empty):
            for arguments in (("check", "-f", "vmdk", str(result.destination)),
                              ("compare", "-f", "vmdk", "-F", "raw",
                               str(result.destination), str(result.source))):
                with self.subTest(arguments=arguments):
                    command = subprocess.run([QEMU_IMG, *arguments], capture_output=True,
                                             text=True, timeout=30)
                    self.assertEqual(command.returncode, 0, command.stdout + command.stderr)


class ProgressTests(unittest.TestCase):
    def test_source_read_speed_target_and_eta(self):
        with patch.object(pv.time, "monotonic", side_effect=[0, 2, 4]), \
                patch("builtins.print") as output, patch.object(pv, "log") as log:
            progress = pv._make_progress("disk0", 8 << 20, source_read=True)
            progress(4 << 20, 8 << 20)
            progress(8 << 20, 8 << 20)
        first, final = (entry.args[0] for entry in output.call_args_list)
        self.assertIn("50%  4/8 MiB", first)
        self.assertIn("2.0 read MiB/s", first)
        self.assertIn("ETA 2s", first)
        self.assertIn("100%  8/8 MiB", final)
        self.assertEqual(log.info.call_args.args[1:7], ("disk0", 100, 8, 8, 2.0, "read MiB/s"))

    def test_empty_source_finishes_at_100_percent_without_division_by_zero(self):
        with patch.object(pv.time, "monotonic", side_effect=[0, 2]), \
                patch("builtins.print") as output, patch.object(pv, "log"):
            pv._make_progress("disk0", 0, source_read=True)(0, 0)
        self.assertIn("100%  0/0 MiB", output.call_args.args[0])
        self.assertIn("0.0 read MiB/s", output.call_args.args[0])
        self.assertIn("ETA 0s", output.call_args.args[0])
        output.assert_called_once()

    def test_leading_holes_have_unknown_eta_until_data_is_processed(self):
        with patch.object(pv.time, "monotonic", side_effect=[0, 2]), \
                patch("builtins.print") as output, patch.object(pv, "log"):
            pv._make_progress("disk0", 8 << 20, source_read=True)(0, 8 << 20)
        self.assertIn("0%  0/8 MiB", output.call_args.args[0])
        self.assertIn("0.0 read MiB/s", output.call_args.args[0])
        self.assertIn("ETA --", output.call_args.args[0])

    def test_packing_throughput_label_is_unchanged(self):
        with patch.object(pv.time, "monotonic", side_effect=[0, 2]), \
                patch("builtins.print") as output, patch.object(pv, "log"):
            pv._make_progress("pack:disk0", 4 << 20)(4 << 20, 4 << 20)
        self.assertIn("2.0 MiB/s", output.call_args.args[0])
        self.assertNotIn("read MiB/s", output.call_args.args[0])


class VmConfigTests(unittest.TestCase):
    current = """# Current configuration; [not-a-section]
name: current-vm
cores: 4
sockets: 2
memory: 8192
bios: ovmf
scsihw: virtio-scsi-single
scsi0: fast-thin:vm-880-disk-0,size=32G
virtio1: file=fast-thin:vm-880-disk-1,size=16G
sata2: archive-thin:vm-880-disk-2,size=8G
ide2: local:iso/installer.iso,media=cdrom
unused0: old-storage:vm-880-disk-9
net0: virtio=00:11:22:33:44:55,bridge=vmbr-current
"""

    def parse(self, text):
        with patch.object(pv.Path, "exists", return_value=True), \
                patch.object(pv.Path, "read_text", return_value=text) as read:
            config = pv._vm_config(880)
        read.assert_called_once_with()
        return config

    def test_current_configuration_without_snapshots(self):
        self.assertEqual(self.parse(self.current), {
            "name": "current-vm", "cores": 4, "sockets": 2, "vcpus": 8,
            "memory": 8192, "bios": "ovmf", "scsihw": "virtio-scsi-single",
            "disks": ["fast-thin:vm-880-disk-0", "fast-thin:vm-880-disk-1",
                      "archive-thin:vm-880-disk-2"],
            "networks": ["vmbr-current"],
        })

    def test_snapshots_cannot_duplicate_disks_or_override_current_settings(self):
        snapshots = """
   [before-upgrade]
name: old-vm
cores: 1
sockets: 1
memory: 512
bios: seabios
scsihw: lsi
scsi0: fast-thin:vm-880-disk-0,size=32G
scsi1: old-storage:vm-880-disk-7,size=8G
net0: virtio=00:11:22:33:44:55,bridge=vmbr-old
efidisk0: old-storage:vm-880-disk-8

[older-snapshot]
virtio0: removed-storage:vm-880-disk-6,size=4G
memory: not-a-current-value
"""
        with patch.object(pv, "log") as log:
            self.assertEqual(self.parse(self.current + snapshots), self.parse(self.current))
            log.warning.assert_not_called()

    def test_snapshot_only_disks_are_not_exported(self):
        config = self.parse("name: diskless\n\n[old]\nscsi0: old-storage:vm-880-disk-0\n")
        self.assertEqual(config["disks"], [])
        self.assertEqual(config["name"], "diskless")

    def test_pending_and_snapshot_sections_are_not_current_configuration(self):
        sections = ("[PENDING]\nscsi0: future-storage:vm-880-disk-0\ncores: 16\n",
                    "[snapshot]\nscsi1: old-storage:vm-880-disk-1\n")
        for suffix in (sections[0], "".join(sections), "".join(reversed(sections))):
            with self.subTest(suffix=suffix):
                self.assertEqual(self.parse(self.current + suffix), self.parse(self.current))


class MainTests(TemporaryTestCase):
    @contextmanager
    def environment(self, flags=(), disks=1, real_writer=False):
        source = self.source(2 * GRAIN + 512, [(512, b"A" * 512), (2 * GRAIN, b"Z" * 512)])
        state = SimpleNamespace(source=source, writers=[], events=[], failure=None,
                                fail_disk=0, output=self.directory / "out", tmp=self.directory / "tmp")
        config = dict(name="synthetic", vcpus=2, memory=1024, bios="seabios", scsihw="lsi",
                      disks=[f"arbitrary-storage:disk-{i}" for i in range(disks)], networks=["bridge-west"])
        originals = {signal.SIGINT: object(), signal.SIGTERM: object()}

        def run(*command):
            self.assertEqual(command[:2], ("pvesm", "path"))
            self.assertIn(command[2], config["disks"])
            return subprocess.CompletedProcess(command, 0, str(source) + "\n", "")

        def writer(**kwargs):
            index = len(state.writers)
            state.writers.append(kwargs)

            def convert():
                state.events.append("convert")
                payload = f"synthetic disk {index}".encode()
                kwargs["dst"].write_bytes(payload)
                if state.failure is not None and index == state.fail_disk:
                    raise state.failure
                return hashlib.sha256(payload).hexdigest()

            return SimpleNamespace(convert=convert)

        def thin_map(*args):
            state.events.append("map")
            return [(512, 1024), (2 * GRAIN, 2 * GRAIN + 512)]

        with ExitStack() as stack:
            stack.enter_context(patch.object(pv.sys, "argv", ["pvstream2ova", "--vmid", "880",
                "--out", str(state.output), "--tmp", str(state.tmp), "--workers", "2", *flags]))
            stack.enter_context(patch.object(pv.os, "geteuid", return_value=0))
            stack.enter_context(patch.object(pv, "_setup_logging"))
            stack.enter_context(patch.object(pv, "log"))
            stack.enter_context(patch("builtins.print"))
            state.status = stack.enter_context(patch.object(pv, "_vm_status", return_value="stopped"))
            stack.enter_context(patch.object(pv, "_vm_config", return_value=config))
            state.storage = stack.enter_context(patch.object(pv, "_check_disk_storages"))
            state.run = stack.enter_context(patch.object(pv, "_run", side_effect=run))
            state.lv = stack.enter_context(patch.object(pv, "_lv", side_effect=lambda action, path:
                                                        state.events.append(action)))
            state.size = stack.enter_context(patch.object(pv, "_source_size", return_value=source.stat().st_size))
            state.tools = stack.enter_context(patch.object(pv, "_check_thin_tools"))
            state.map = stack.enter_context(patch.object(pv, "_thin_map", side_effect=thin_map))
            state.reserve = stack.enter_context(patch.object(pv, "_thin_reserved_map",
                                                          side_effect=AssertionError("unexpected reservation")))
            state.progress = stack.enter_context(patch.object(pv, "_make_progress", return_value=lambda *_: None))
            stack.enter_context(patch.object(pv, "_punch_hole"))
            state.signals = stack.enter_context(patch.object(pv.signal, "signal", side_effect=lambda sig, handler:
                                                             originals[sig]))
            if not real_writer:
                state.writer = stack.enter_context(patch.object(pv, "VmdkWriter", side_effect=writer))
            state.verify = stack.enter_context(patch.object(pv, "_verify_vmdk"))
            yield state
            self.assertEqual(state.signals.call_args_list[-2:],
                             [call(sig, handler) for sig, handler in originals.items()])
            self.assertEqual(list(state.tmp.glob("*.vmdk")), [])

    def assert_manifest(self, path):
        with tarfile.open(path) as archive:
            names = archive.getnames()
            self.assertEqual(names[:2], ["synthetic.ovf", "synthetic.mf"])
            self.assertTrue(all(name.endswith(".vmdk") for name in names[2:]))
            payloads = {name: archive.extractfile(name).read() for name in names}
        manifest = payloads["synthetic.mf"].decode().splitlines()
        self.assertEqual(len(manifest), len(names) - 1)
        for name in [names[0], *names[2:]]:
            self.assertIn(f"SHA256({name})= {hashlib.sha256(payloads[name]).hexdigest()}", manifest)
        ET.fromstring(payloads["synthetic.ovf"])
        return payloads

    def test_default_maps_before_conversion_and_packs_matching_manifest(self):
        with self.environment(disks=2) as state:
            pv.main()
            self.assertEqual(state.events, ["y", "map", "convert", "n"] * 2)
            state.tools.assert_called_once_with()
            self.assertEqual(state.map.call_count, 2)
            self.assertEqual(state.status.call_count, 5)
            for arguments in state.writers:
                self.assertEqual(arguments["mapped_ranges"], [(512, 1024), (2 * GRAIN, 2 * GRAIN + 512)])
                self.assertEqual(arguments["src_size"], 2 * GRAIN + 512)
            state.storage.assert_called_once_with(["arbitrary-storage:disk-0", "arbitrary-storage:disk-1"])
            payloads = self.assert_manifest(state.output / "synthetic.ova")
            self.assertEqual(payloads["synthetic-disk1.vmdk"], b"synthetic disk 1")
            self.assertIn(call("disk0", 1024, source_read=True), state.progress.call_args_list)

    def test_full_read_bypasses_all_thin_metadata_and_preserves_zero_omission(self):
        real_pread = os.pread
        with self.environment(flags=("--no-thin-map",), real_writer=True) as state, \
                patch.object(pv.os, "pread", wraps=real_pread) as pread:
            pv.main()
            state.tools.assert_not_called()
            state.map.assert_not_called()
            state.reserve.assert_not_called()
            self.assertEqual(state.size.call_count, 2)
            self.assertIn(call("disk0", 2 * GRAIN + 512, source_read=True), state.progress.call_args_list)
            self.assertEqual(pread.call_count, 1)
            self.assertEqual(pread.call_args.args[1:], (2 * GRAIN + 512, 0))
            payloads = self.assert_manifest(state.output / "synthetic.ova")
            decoded = decode_vmdk(self, payloads["synthetic-disk0.vmdk"], 2 * GRAIN + 512)
            assert_logical_contents(self, decoded, 2 * GRAIN + 512,
                                    [(512, b"A" * 512), (2 * GRAIN, b"Z" * 512)])
            self.assertEqual(decoded.tables[0][1], 0)

    def test_conversion_failures_interrupts_and_signal_handler_cleanup(self):
        for failure in (RuntimeError("conversion failed"), KeyboardInterrupt(), SystemExit("SIGTERM")):
            with self.subTest(failure=type(failure)), self.environment(disks=2) as state:
                state.failure, state.fail_disk = failure, 1
                expected = SystemExit if isinstance(failure, Exception) else type(failure)
                with self.assertRaises(expected):
                    pv.main()
                self.assertEqual(state.lv.call_args_list,
                                 [call("y", str(state.source)), call("n", str(state.source))] * 2)
                self.assertFalse((state.output / "synthetic.ova").exists())
        with self.environment() as state:
            def interrupted(**kwargs):
                kwargs["dst"].write_bytes(b"partial")
                handler = state.signals.call_args_list[0].args[1]
                return SimpleNamespace(convert=lambda: handler(signal.SIGINT, None))
            state.writer.side_effect = interrupted
            with self.assertRaisesRegex(SystemExit, "Interrupted"):
                pv.main()
            self.assertEqual(state.events[-1], "n")

    def test_activation_sizing_and_map_failures_deactivate_without_fallback(self):
        for stage in ("lv", "size", "map"):
            with self.subTest(stage=stage), self.environment() as state:
                target = getattr(state, stage)
                target.side_effect = [RuntimeError(f"{stage} failed"), None] if stage == "lv" else RuntimeError(f"{stage} failed")
                with self.assertRaisesRegex(SystemExit, f"{stage} failed"):
                    pv.main()
                self.assertEqual(state.lv.call_args_list[-1], call("n", str(state.source)))
                state.writer.assert_not_called()
                self.assertFalse((state.output / "synthetic.ova").exists())

    def test_missing_tools_cleanup_and_vm_running_guards(self):
        with self.environment() as state:
            state.tools.side_effect = RuntimeError("missing thin tools")
            with self.assertRaisesRegex(SystemExit, "missing thin tools"):
                pv.main()
            state.lv.assert_not_called()
            state.map.assert_not_called()
            state.writer.assert_not_called()
        for statuses, converted in ((["stopped", "running"], False),
                                    (["stopped", "stopped", "running"], True)):
            with self.subTest(statuses=statuses), self.environment() as state:
                state.status.side_effect = statuses
                with self.assertRaisesRegex(SystemExit, "remain stopped"):
                    pv.main()
                self.assertEqual(state.writer.called, converted)
                self.assertEqual(state.lv.call_args_list[-1], call("n", str(state.source)))
                self.assertFalse((state.output / "synthetic.ova").exists())

    def test_verification_failure_cleans_converted_files(self):
        with self.environment(flags=("--verify",)) as state:
            state.verify.side_effect = SystemExit("invalid VMDK")
            with self.assertRaisesRegex(SystemExit, "invalid VMDK"):
                pv.main()
            state.verify.assert_called_once()
            self.assertEqual(state.events[-1], "n")
            self.assertFalse((state.output / "synthetic.ova").exists())


if __name__ == "__main__":
    unittest.main()
