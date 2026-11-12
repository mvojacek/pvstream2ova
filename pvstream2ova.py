#!/usr/bin/env python3
"""pvstream2ova — Export Proxmox VM to OVA with streaming hole-punch and parallel VMDK compression.

Native VMDK streamOptimized writer: 64 KiB grains compressed in parallel via ThreadPoolExecutor.
Peak disk usage = one VMDK; freed by fallocate hole-punching while streaming into the OVA tar.
Generates OVF 1.0 descriptor and SHA256 manifest (.mf) for VMware/VirtualBox compatibility.

Usage: pvstream2ova.py --vmid <ID> [--out <dir>] [--tmp <dir>] [--name <name>]
                       [--workers N] [--level 1-9] [--log <file>] [--verify] [--no-thin-map]
"""

from __future__ import annotations

import argparse
import ctypes
import hashlib
import logging
import os
import re
import select
import shutil
import signal
import stat
import struct
import subprocess
import sys
import tempfile
import time
import xml.etree.ElementTree as ET
import zlib
from concurrent.futures import ThreadPoolExecutor
from contextlib import contextmanager
from pathlib import Path
from typing import BinaryIO, Callable

log = logging.getLogger("pvstream2ova")

# I/O buffer for reading the LVM block device
CHUNK        = 64 << 20

# VMDK streamOptimized grain = 64 KiB; GRAIN_SECTS = grain / 512-byte sector
GRAIN_SIZE   = 65536
GRAIN_SECTS  = 128

# One grain table entry covers GT_COVERAGE grains = 32 MiB of virtual disk;
# BATCH_GRAINS grains are compressed per parallel batch (16 MiB raw)
GT_COVERAGE  = 512
BATCH_GRAINS = 256

VMDK_MAGIC   = 0x564D444B
VMDK_VER     = 3
_MARKER_EOS  = 0
_MARKER_GT   = 1
_MARKER_GD   = 2
_MARKER_FOOT = 3

# Descriptor region: 20 sectors reserved by the streamOptimized spec
_DESC_BYTES  = 20 * 512

_libc  = ctypes.CDLL("libc.so.6", use_errno=True)
# FALLOC_FL_KEEP_SIZE | FALLOC_FL_PUNCH_HOLE — free blocks without changing file size
_PUNCH = 0x01 | 0x02


def _punch_hole(fd: int, offset: int, length: int) -> None:
    _libc.fallocate(ctypes.c_int(fd), ctypes.c_int(_PUNCH),
                    ctypes.c_long(offset), ctypes.c_long(length))


# ── TAR ustar (OVA container) ─────────────────────────────────────────────────

def _tar_header(name: str, size: int) -> bytes:
    h = bytearray(512)

    def put_str(val, off, width):
        b = (val.encode() if isinstance(val, str) else val)[:width]
        h[off:off + len(b)] = b

    def put_oct(val, off, width):
        put_str(f"{val:0{width - 1}o}\x00", off, width)

    put_str(name[:99], 0, 100)
    put_oct(0o644, 100, 8)
    put_oct(0, 108, 8)
    put_oct(0, 116, 8)
    put_oct(size, 124, 12)
    put_oct(int(time.time()), 136, 12)
    h[156] = ord("0")
    h[257:265] = b"ustar\x0000"
    h[148:156] = b"        "
    put_str(f"{sum(h):06o}\x00 ", 148, 8)
    return bytes(h)


class OvaWriter:
    def __init__(self, path: Path) -> None:
        self._f = path.open("wb")

    def add_bytes(self, name: str, data: bytes) -> None:
        self._f.write(_tar_header(name, len(data)))
        self._f.write(data)
        pad = (-len(data)) % 512
        if pad:
            self._f.write(b"\x00" * pad)

    def add_file(self, name: str, path: Path,
                 on_progress: Callable[[int, int], None] | None = None) -> None:
        """Stream file into OVA with hole-punching; deletes source when done."""
        size = path.stat().st_size
        self._f.write(_tar_header(name, size))
        fd = os.open(str(path), os.O_RDWR)
        written = 0
        try:
            while written < size:
                to_read = min(CHUNK, size - written)
                chunk   = os.read(fd, to_read)
                if not chunk:
                    break
                self._f.write(chunk)
                _punch_hole(fd, written, len(chunk))
                written += len(chunk)
                if on_progress:
                    on_progress(written, size)
        finally:
            os.close(fd)
        path.unlink()
        pad = (-size) % 512
        if pad:
            self._f.write(b"\x00" * pad)

    def close(self) -> None:
        # TAR EOF: two consecutive 512-byte zero blocks required by the ustar spec
        self._f.write(b"\x00" * 10240)
        self._f.flush()
        os.fsync(self._f.fileno())
        self._f.close()

    def __enter__(self): return self
    def __exit__(self, *_): self.close()


# ── VMDK streamOptimized ──────────────────────────────────────────────────────

def _vmdk_header(capacity_sectors: int, gd_offset: int, rgd_offset: int = 0) -> bytes:
    # bit0=newline-detection, bit16=compressed-grains, bit17=markers
    flags = (1 << 0) | (1 << 16) | (1 << 17)
    buf = bytearray(512)
    struct.pack_into("<I", buf,  0, VMDK_MAGIC)
    struct.pack_into("<I", buf,  4, VMDK_VER)
    struct.pack_into("<I", buf,  8, flags)
    struct.pack_into("<Q", buf, 12, capacity_sectors)
    struct.pack_into("<Q", buf, 20, GRAIN_SECTS)
    struct.pack_into("<Q", buf, 28, 1)           # descriptorOffset
    struct.pack_into("<Q", buf, 36, 20)          # descriptorSize
    struct.pack_into("<I", buf, 44, GT_COVERAGE)
    struct.pack_into("<Q", buf, 48, rgd_offset)
    struct.pack_into("<Q", buf, 56, gd_offset)
    struct.pack_into("<Q", buf, 64, 128)         # overHead: first grain at sector 128
    buf[72] = 0
    buf[73] = ord('\n'); buf[74] = ord(' '); buf[75] = ord('\r'); buf[76] = ord('\n')
    struct.pack_into("<H", buf, 77, 1)           # compressAlgorithm: deflate
    return bytes(buf)


def _vmdk_descriptor(name: str, capacity_sectors: int) -> bytes:
    text = (
        "# Disk DescriptorFile\n"
        "version=1\n"
        "CID=fffffffe\n"
        "parentCID=ffffffff\n"
        'createType="streamOptimized"\n'
        "\n"
        "# Extent description\n"
        f'RDONLY {capacity_sectors} STREAMOPTIMIZED "{name}.vmdk"\n'
        "\n"
        "#DDB\n"
        "\n"
        'ddb.virtualHWVersion = "19"\n'
        'ddb.geometry.cylinders = "0"\n'
        'ddb.geometry.heads = "255"\n'
        'ddb.geometry.sectors = "63"\n'
        'ddb.adapterType = "lsilogic"\n'
    )
    raw = text.encode("ascii")
    return raw + b"\x00" * (_DESC_BYTES - len(raw))


def _meta_marker(num_data_sectors: int, mtype: int) -> bytes:
    buf = bytearray(512)
    struct.pack_into("<QII", buf, 0, num_data_sectors, 0, mtype)
    return bytes(buf)


def _pread_exact(fd: int, size: int, offset: int) -> bytes:
    data = os.pread(fd, size, offset)
    if len(data) == size:
        return data
    result = bytearray(data)
    while len(result) < size:
        if not data:
            raise EOFError(f"Premature EOF at source byte {offset + len(result)}; "
                           f"expected {size} bytes at {offset}")
        data = os.pread(fd, size - len(result), offset + len(result))
        result.extend(data)
    return bytes(result)


def _compress_batch(raw: bytes | bytearray, level: int,
                    mapped_grains: bytearray | None = None) -> list[bytes | None]:
    results = []
    for gi, offset in enumerate(range(0, len(raw), GRAIN_SIZE)):
        if mapped_grains is not None and not mapped_grains[gi]:
            results.append(None)
            continue
        grain = raw[offset:offset + GRAIN_SIZE]
        results.append(None if not any(grain) else zlib.compress(grain, level=level))
    return results


class _HashingFile:
    """Wraps a writable file to compute SHA256 of everything written."""
    def __init__(self, f) -> None:
        self._f = f
        self._h = hashlib.sha256()

    def write(self, data: bytes) -> int:
        self._f.write(data)
        self._h.update(data)
        return len(data)

    def hexdigest(self) -> str:
        return self._h.hexdigest()


class VmdkWriter:
    def __init__(self, src: str, dst: Path, workers: int, level: int = 6,
                 on_progress: Callable[[int, int], None] | None = None,
                 mapped_ranges: list[tuple[int, int]] | None = None,
                 src_size: int | None = None) -> None:
        if workers < 1:
            raise ValueError("Compression workers must be positive")
        self._src      = src
        self._dst      = dst
        self._workers  = workers
        self._level    = level
        self._progress = on_progress
        self._ranges   = mapped_ranges
        self._size     = src_size

    def convert(self) -> str:
        """Convert LVM block device to VMDK streamOptimized; returns SHA256 of output."""
        src_size = _source_size(self._src)
        if self._size is not None and src_size != self._size:
            raise RuntimeError("Source capacity changed after thin-map capture")
        previous_end = 0
        if self._ranges is not None:
            for start, end in self._ranges:
                if not (0 <= previous_end <= start < end <= src_size):
                    raise ValueError("Mapped ranges must be ordered, non-overlapping and in capacity")
                previous_end = end
        capacity_sectors = src_size // 512
        n_grains         = (src_size + GRAIN_SIZE - 1) // GRAIN_SIZE

        src_fd = os.open(self._src, os.O_RDONLY)
        try:
            with self._dst.open("wb") as raw_f, \
                 ThreadPoolExecutor(max_workers=self._workers) as pool:
                hf = _HashingFile(raw_f)
                self._write(hf, pool, src_fd, src_size, capacity_sectors, n_grains)
                return hf.hexdigest()
        finally:
            os.close(src_fd)

    def _write(self, f, pool, src_fd, src_size, capacity_sectors, n_grains) -> None:
        name       = self._dst.stem
        cur_sector = 0

        def write_sectors(data: bytes) -> None:
            nonlocal cur_sector
            f.write(data)
            cur_sector += len(data) // 512

        # gd_offset placeholder: streamOptimized readers use the footer, not the primary header
        write_sectors(_vmdk_header(capacity_sectors, gd_offset=0xFFFFFFFFFFFFFFFF))
        write_sectors(_vmdk_descriptor(name, capacity_sectors))

        if cur_sector < 128:
            f.write(b"\x00" * ((128 - cur_sector) * 512))
            cur_sector = 128

        grain_offsets = [0] * n_grains
        gd_entries    = []

        def flush_gt(block_start: int) -> None:
            nonlocal cur_sector
            entries = grain_offsets[block_start:block_start + GT_COVERAGE]
            entries += [0] * (GT_COVERAGE - len(entries))
            write_sectors(_meta_marker(4, _MARKER_GT))
            gd_entries.append(cur_sector)           # points to GT data, after marker
            f.write(struct.pack(f"<{GT_COVERAGE}I", *entries))
            cur_sector += 4

        pending      = []
        next_submit  = 0
        range_cursor = 0

        def submit_next() -> None:
            nonlocal next_submit, range_cursor
            if next_submit >= n_grains:
                return
            bs = next_submit
            count = min(BATCH_GRAINS, n_grains - bs)
            start = bs * GRAIN_SIZE
            end = min(start + count * GRAIN_SIZE, src_size)
            mapped_grains = None
            raw = None
            if self._ranges is None:
                raw = _pread_exact(src_fd, end - start, start)
                raw += b"\x00" * (count * GRAIN_SIZE - len(raw))
            else:
                while range_cursor < len(self._ranges):
                    lo, hi = self._ranges[range_cursor]
                    if lo >= end:
                        break
                    lo, stop = max(lo, start), min(hi, end)
                    if lo < stop:
                        if raw is None:
                            raw = bytearray(count * GRAIN_SIZE)
                            mapped_grains = bytearray(count)
                        raw[lo - start:stop - start] = _pread_exact(src_fd, stop - lo, lo)
                        first = (lo - start) // GRAIN_SIZE
                        last = (stop - start - 1) // GRAIN_SIZE + 1
                        mapped_grains[first:last] = b"\x01" * (last - first)
                    if hi > end:
                        break
                    range_cursor += 1
            future = (pool.submit(_compress_batch, raw, self._level, mapped_grains)
                      if raw is not None else None)
            pending.append((bs, count, future))
            next_submit += count

        # Prefill queue with 2× workers batches so threads stay busy while results are consumed
        for _ in range(self._workers * 2):
            submit_next()

        grains_done = 0
        while pending:
            batch_start, count, future = pending.pop(0)
            submit_next()
            compressed = future.result() if future is not None else [None] * count
            if len(compressed) != count or batch_start != grains_done:
                raise RuntimeError("Invalid compression batch grain count or ordering")
            for ci, cdata in enumerate(compressed):
                gi = batch_start + ci
                if cdata is not None:
                    grain_offsets[gi] = cur_sector
                    blob = struct.pack("<QI", gi * GRAIN_SECTS, len(cdata)) + cdata
                    pad  = (-len(blob)) % 512
                    f.write(blob + b"\x00" * pad)
                    cur_sector += (len(blob) + pad) // 512
                grains_done += 1
                if grains_done % GT_COVERAGE == 0:
                    flush_gt(grains_done - GT_COVERAGE)
                if self._progress:
                    self._progress(min(grains_done * GRAIN_SIZE, src_size), src_size)

        if grains_done % GT_COVERAGE:
            flush_gt(grains_done - grains_done % GT_COVERAGE)
        if grains_done != n_grains or len(gd_entries) != (n_grains + GT_COVERAGE - 1) // GT_COVERAGE:
            raise RuntimeError("Incomplete VMDK grain tables")

        gd_data  = struct.pack(f"<{len(gd_entries)}I", *gd_entries)
        gd_pad   = (-len(gd_data)) % 512
        gd_sects = (len(gd_data) + gd_pad) // 512
        write_sectors(_meta_marker(gd_sects, _MARKER_GD))
        gd_data_sector = cur_sector                 # points to GD data, after marker
        f.write(gd_data + b"\x00" * gd_pad)
        cur_sector += gd_sects

        # qemu reads footer at file_size-1536: [FOOT marker][Footer][EOS]
        write_sectors(_meta_marker(1, _MARKER_FOOT))
        write_sectors(_vmdk_header(capacity_sectors, gd_offset=gd_data_sector, rgd_offset=0))
        write_sectors(_meta_marker(0, _MARKER_EOS))


# ── Proxmox helpers ───────────────────────────────────────────────────────────

def _run(*cmd: str, check: bool = True, timeout: float | None = None) -> subprocess.CompletedProcess:
    return subprocess.run(list(cmd), check=check, capture_output=True, text=True, timeout=timeout)


def _thin_uint(value: str, field: str) -> int:
    if not re.fullmatch(r"[0-9]+", value):
        raise ValueError(f"Invalid {field}: {value[:80]!r}")
    return int(value)


def _thin_error(exc: BaseException) -> str:
    detail = str(exc)
    if isinstance(exc, subprocess.CalledProcessError):
        output = exc.stderr or exc.stdout or ""
        if isinstance(output, bytes):
            output = output.decode("utf-8", errors="replace")
        detail += f": {output.strip()}" if output else ""
    return detail[:4096]


def _source_size(src: str) -> int:
    try:
        size = _thin_uint(_run("blockdev", "--getsize64", src).stdout.strip(), "source size")
        if size <= 0 or size % 512:
            raise ValueError(f"Source size must be positive and 512-byte aligned, got {size}")
        return size
    except (OSError, ValueError, subprocess.CalledProcessError) as exc:
        raise RuntimeError(
            f"Cannot size {src}: {_thin_error(exc)}; ensure the LV is active and "
            "blockdev (util-linux) is installed") from exc


def _check_thin_tools() -> None:
    missing = [name for name in ("dmsetup", "thin_dump") if shutil.which(name) is None]
    if missing:
        raise RuntimeError(
            f"Missing thin-map tools: {', '.join(missing)}; install dmsetup and "
            "thin-provisioning-tools (provides thin_dump), or use --no-thin-map "
            "to read the full device")


def _thin_target(output: str, target: str) -> tuple[int, list[str]]:
    lines = [line.split() for line in output.splitlines() if line.strip()]
    if len(lines) != 1 or len(lines[0]) < 3:
        raise ValueError(f"Expected one {target} target, not a stacked or multi-segment layout")
    fields = lines[0]
    start = _thin_uint(fields[0], "target start")
    length = _thin_uint(fields[1], "target length")
    if start != 0 or length == 0 or fields[2] != target:
        raise ValueError(f"Expected a positive, zero-based {target} target")
    return length, fields[3:]


def _thin_devno(value: str) -> tuple[int, int]:
    if not re.fullmatch(r"[0-9]+:[0-9]+", value):
        raise ValueError(f"Expected device major:minor, got {value[:80]!r}")
    major, minor = value.split(":")
    return int(major), int(minor)


def _thin_held_root(pool: tuple[str, ...], pool_length: int) -> int | None:
    length, fields = _thin_target(_run("dmsetup", "status", *pool, timeout=30).stdout, "thin-pool")
    if length != pool_length or len(fields) < 8:
        raise ValueError("Invalid thin-pool status or changed pool size")
    _thin_uint(fields[0], "pool transaction")
    for usage in fields[1:3]:
        parts = usage.split("/")
        if len(parts) != 2:
            raise ValueError("Invalid thin-pool usage counters")
        used, total = (_thin_uint(part, "pool usage") for part in parts)
        if used > total:
            raise ValueError("Thin-pool usage exceeds its capacity")
    if fields[4] not in ("rw", "ro", "out_of_data_space") or fields[7] != "-":
        raise ValueError("Thin pool is failed or needs checking")
    if fields[3] == "-":
        return None
    root = _thin_uint(fields[3], "held metadata root")
    if root == 0:
        raise ValueError("Invalid zero held metadata root")
    return root


def _parse_thin_dump(stream: BinaryIO, thin_id: int, data_block_sectors: int,
                     src_size: int) -> list[tuple[int, int]]:
    if not 0 <= thin_id < (1 << 24):
        raise ValueError("Thin device ID must fit in 24 bits")
    if data_block_sectors <= 0 or src_size <= 0 or src_size % 512:
        raise ValueError("Invalid thin block size or source capacity")
    chunk_bytes = data_block_sectors * 512
    ranges: list[tuple[int, int]] = []
    stack: list[ET.Element] = []
    seen_superblock = False
    seen_device = False
    mapped_blocks = 0
    expected_blocks = 0
    previous_end = 0
    completed = None

    def integer(element: ET.Element, field: str) -> int:
        value = _thin_uint(element.get(field, ""), f"{element.tag}.{field}")
        if value >= (1 << 64):
            raise ValueError(f"{element.tag}.{field} exceeds 64 bits")
        return value

    for event, element in ET.iterparse(stream, events=("start", "end")):
        if completed is not None:
            if completed.tail and completed.tail.strip():
                raise ValueError(f"Unexpected text after thin XML element {completed.tag!r}")
            completed.clear()
            completed = None
        if event == "start":
            if not stack:
                if element.tag != "superblock" or seen_superblock:
                    raise ValueError("Expected exactly one thin metadata superblock")
                seen_superblock = True
                if "uuid" not in element.attrib:
                    raise ValueError("Missing superblock.uuid")
                for field in ("time", "transaction", "nr_data_blocks"):
                    integer(element, field)
                for field in ("flags", "version", "metadata_snap"):
                    if field in element.attrib:
                        integer(element, field)
                if integer(element, "data_block_size") != data_block_sectors:
                    raise ValueError("XML data_block_size does not match the thin-pool table")
            elif len(stack) == 1 and element.tag == "device":
                if seen_device or integer(element, "dev_id") != thin_id:
                    raise ValueError(f"Expected exactly thin device {thin_id}")
                seen_device = True
                expected_blocks = integer(element, "mapped_blocks")
                for field in ("transaction", "creation_time", "snap_time"):
                    integer(element, field)
            elif len(stack) == 2 and element.tag in ("range_mapping", "single_mapping"):
                if stack[-1].tag != "device":
                    raise ValueError("Mapping outside a thin device")
                integer(element, "time")
                if element.tag == "range_mapping":
                    origin = integer(element, "origin_begin")
                    length = integer(element, "length")
                    integer(element, "data_begin")
                else:
                    origin = integer(element, "origin_block")
                    length = 1
                    integer(element, "data_block")
                end = origin + length
                if length == 0 or end > (1 << 64) or origin < previous_end:
                    raise ValueError("Invalid, unordered or overlapping thin mapping")
                previous_end = end
                mapped_blocks += length
                if mapped_blocks > expected_blocks:
                    raise ValueError("Thin mappings exceed device.mapped_blocks")
                start_byte = origin * chunk_bytes
                end_byte = min(end * chunk_bytes, src_size)
                if start_byte < end_byte:
                    if ranges and ranges[-1][1] == start_byte:
                        ranges[-1] = (ranges[-1][0], end_byte)
                    else:
                        ranges.append((start_byte, end_byte))
            else:
                raise ValueError(f"Unsupported thin XML element: {element.tag!r}")
            stack.append(element)
        else:
            if element.text and element.text.strip():
                raise ValueError(f"Unexpected text in thin XML element {element.tag!r}")
            if element.tag == "device" and mapped_blocks != expected_blocks:
                raise ValueError("Thin mapping count does not match device.mapped_blocks")
            stack.pop()
            if stack:
                stack[-1].remove(element)
            completed = element
    if not seen_superblock or not seen_device or stack:
        raise ValueError(f"Missing or incomplete metadata for thin device {thin_id}")
    return ranges


def _stop_thin_dump(pid: int) -> None:
    try:
        if os.waitpid(pid, os.WNOHANG)[0]:
            return
        try:
            os.kill(pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        deadline = time.monotonic() + 5
        while time.monotonic() < deadline:
            if os.waitpid(pid, os.WNOHANG)[0]:
                return
            time.sleep(0.05)
        try:
            os.kill(pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        os.waitpid(pid, 0)
    except ChildProcessError:
        pass


@contextmanager
def _deferred_termination():
    pending = []
    handlers = {}

    def defer(sig, _frame):
        pending.append(sig)

    def check():
        if pending:
            raise SystemExit(f"Interrupted (signal {pending[0]})")

    try:
        for sig in (signal.SIGINT, signal.SIGTERM):
            handlers[sig] = signal.signal(sig, defer)
        yield check
    finally:
        previous_mask = signal.pthread_sigmask(signal.SIG_BLOCK, {signal.SIGINT, signal.SIGTERM})
        try:
            for sig, handler in handlers.items():
                signal.signal(sig, handler)
        finally:
            signal.pthread_sigmask(signal.SIG_SETMASK, previous_mask)
        if sys.exc_info()[0] is None:
            check()


class _ThinDumpReader:
    def __init__(self, stream, check_interrupt):
        self._stream = stream
        self._check = check_interrupt

    def read(self, size):
        while True:
            self._check()
            if select.select([self._stream], [], [], 0.1)[0]:
                return self._stream.read(size)


def _thin_reserved_map(pool: tuple[str, ...], pool_length: int, metadata: str,
                       thin_id: int, data_block_sectors: int,
                       src_size: int) -> list[tuple[int, int]]:
    identity = f"{pool[1]}:{pool[3]}"
    if _thin_held_root(pool, pool_length) is not None:
        raise RuntimeError(f"Pool {identity} already has a metadata reservation; leaving it untouched")
    owned = False
    pid = None
    read_fd = write_fd = None
    signals = {signal.SIGINT, signal.SIGTERM}
    recovery = (f"Pool {identity}, metadata {metadata}: after confirming no thin_dump or other "
                f"metadata reader remains, inspect dmsetup status {' '.join(pool)} and, "
                f"if our reservation is still held, run dmsetup message {' '.join(pool)} "
                "0 release_metadata_snap")
    with _deferred_termination() as check_interrupt, tempfile.TemporaryFile() as errors:
        try:
            try:
                check_interrupt()
                previous_mask = signal.pthread_sigmask(signal.SIG_BLOCK, signals)
                try:
                    _run("dmsetup", "message", *pool, "0", "reserve_metadata_snap")
                    owned = True
                finally:
                    signal.pthread_sigmask(signal.SIG_SETMASK, previous_mask)
                check_interrupt()
                root = _thin_held_root(pool, pool_length)
                check_interrupt()
                if root is None:
                    raise RuntimeError(f"Pool {identity} did not expose the reserved metadata root")
                command = ["thin_dump", "--format", "xml", "--dev-id", str(thin_id),
                           f"--metadata-snap={root}", metadata]
                previous_mask = signal.pthread_sigmask(signal.SIG_BLOCK, signals)
                try:
                    read_fd, write_fd = os.pipe()
                    pid = os.posix_spawnp(
                        command[0], command, os.environ,
                        file_actions=[(os.POSIX_SPAWN_DUP2, write_fd, 1),
                                      (os.POSIX_SPAWN_DUP2, errors.fileno(), 2),
                                      (os.POSIX_SPAWN_CLOSE, read_fd),
                                      (os.POSIX_SPAWN_CLOSE, write_fd)],
                        setsigmask=previous_mask, setsigdef=(signal.SIGPIPE,))
                    os.close(write_fd)
                    write_fd = None
                finally:
                    signal.pthread_sigmask(signal.SIG_SETMASK, previous_mask)
                with os.fdopen(read_fd, "rb", buffering=0) as stream:
                    read_fd = None
                    reader = _ThinDumpReader(stream, check_interrupt)
                    ranges = _parse_thin_dump(reader, thin_id, data_block_sectors, src_size)
                while True:
                    check_interrupt()
                    finished, status = os.waitpid(pid, os.WNOHANG)
                    if finished:
                        break
                    time.sleep(0.05)
                pid = None
                returncode = os.waitstatus_to_exitcode(status)
                if returncode:
                    raise RuntimeError(f"thin_dump exited with status {returncode}")
                return ranges
            finally:
                original_error = sys.exc_info()[1]
                cleanup_error = None
                previous_mask = signal.pthread_sigmask(signal.SIG_BLOCK, signals)
                try:
                    if pid is not None:
                        try:
                            _stop_thin_dump(pid)
                        except Exception as exc:
                            cleanup_error = RuntimeError(
                                f"Cannot terminate/reap thin_dump PID {pid}; reservation retained. "
                                f"{recovery}. Failure: {_thin_error(exc)}")
                    for fd in (read_fd, write_fd):
                        if fd is not None:
                            try:
                                os.close(fd)
                            except OSError as exc:
                                log.warning("Cannot close thin_dump pipe: %s", _thin_error(exc))
                    if owned and cleanup_error is None:
                        try:
                            _run("dmsetup", "message", *pool, "0", "release_metadata_snap")
                        except Exception as exc:
                            cleanup_error = RuntimeError(
                                f"Cannot release our metadata reservation. {recovery}. "
                                f"Failure: {_thin_error(exc)}")
                    if cleanup_error is not None:
                        if original_error is not None:
                            log.error("%s; preserving original failure: %s", cleanup_error,
                                      _thin_error(original_error))
                        else:
                            raise cleanup_error
                finally:
                    signal.pthread_sigmask(signal.SIG_SETMASK, previous_mask)
        except Exception as exc:
            errors.seek(0, os.SEEK_END)
            size = errors.tell()
            errors.seek(max(0, size - 4096))
            detail = errors.read(4096).decode("utf-8", errors="replace").strip()
            suffix = f"; thin_dump stderr: {detail}" if detail else ""
            raise RuntimeError(f"{_thin_error(exc)}{suffix}") from exc


def _thin_map(lv_path: str, src_size: int) -> list[tuple[int, int]]:
    try:
        _check_thin_tools()
        if src_size <= 0 or src_size % 512:
            raise ValueError("Source capacity must be positive and 512-byte aligned")
        length, fields = _thin_target(_run("dmsetup", "table", lv_path).stdout, "thin")
        if length * 512 != src_size:
            raise ValueError("Thin target does not span the source capacity")
        if len(fields) == 3:
            raise ValueError("External-origin thin devices may contain data in unmapped ranges")
        if len(fields) != 2:
            raise ValueError("Unsupported thin target arguments")
        major, minor = _thin_devno(fields[0])
        thin_id = _thin_uint(fields[1], "thin device ID")
        if thin_id >= (1 << 24):
            raise ValueError("Thin device ID must fit in 24 bits")
        pool = ("-j", str(major), "-m", str(minor))
        pool_length, fields = _thin_target(_run("dmsetup", "table", *pool).stdout, "thin-pool")
        if len(fields) < 4:
            raise ValueError("Incomplete thin-pool target")
        metadata_major, metadata_minor = _thin_devno(fields[0])
        _thin_devno(fields[1])
        data_block_sectors = _thin_uint(fields[2], "pool data block size")
        if not 128 <= data_block_sectors <= 2097152 or data_block_sectors % 128:
            raise ValueError("Invalid thin-pool data block size")
        _thin_uint(fields[3], "pool low water mark")
        if len(fields) > 4 and _thin_uint(fields[4], "pool feature count") != len(fields) - 5:
            raise ValueError("Invalid thin-pool feature count")
        metadata = Path(f"/dev/block/{metadata_major}:{metadata_minor}").resolve(strict=True)
        info = metadata.stat()
        if not stat.S_ISBLK(info.st_mode) or (os.major(info.st_rdev), os.minor(info.st_rdev)) != (
                metadata_major, metadata_minor):
            raise ValueError(f"Metadata path {metadata} is not the expected block device")
        return _thin_reserved_map(pool, pool_length, str(metadata), thin_id,
                                  data_block_sectors, src_size)
    except Exception as exc:
        raise RuntimeError(
            f"Cannot obtain thin map for {lv_path}: {_thin_error(exc)}; "
            "use --no-thin-map to read the full device instead") from exc


def _lv(action: str, lv_path: str) -> None:
    _run("lvchange", f"-a{action}", lv_path, check=(action == "y"))


def _vm_status(vmid: int) -> str:
    return _run("qm", "status", str(vmid)).stdout.split()[-1]


def _check_disk_storages(disks: list[str]) -> None:
    storage_types = {
        name: storage_type
        for storage_type, name in re.findall(
            r"^(\S+):[ \t]+(\S+)", Path("/etc/pve/storage.cfg").read_text(), re.MULTILINE)
    }
    for disk in disks:
        storage = disk.split(":", 1)[0]
        storage_type = storage_types.get(storage)
        if storage_type != "lvmthin":
            raise SystemExit(
                f"Disk {disk}: storage '{storage}' must be lvmthin "
                f"(found {storage_type or 'unknown'})")


def _vm_config(vmid: int) -> dict:
    conf_path = Path(f"/etc/pve/qemu-server/{vmid}.conf")
    if not conf_path.exists():
        raise SystemExit(f"VM {vmid} not found: {conf_path}")

    cfg = {"name": f"vm-{vmid}", "cores": 1, "sockets": 1,
           "memory": 1024, "bios": "seabios", "disks": [],
           "scsihw": "lsi", "networks": []}

    for raw_line in conf_path.read_text().splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("["):
            break
        key, _, val = line.partition(":")
        key = key.strip(); val = val.strip()

        if   key == "name":    cfg["name"]    = val
        elif key == "cores":   cfg["cores"]   = int(val)
        elif key == "sockets": cfg["sockets"] = int(val)
        elif key == "memory":  cfg["memory"]  = int(val)
        elif key == "bios":    cfg["bios"]    = val
        elif key == "scsihw":  cfg["scsihw"]  = val
        elif re.match(r"^net\d+$", key):
            m = re.search(r"bridge=([^,]+)", val)
            if m:
                cfg["networks"].append(m.group(1))
        elif key == "efidisk0":
            log.warning("efidisk0 skipped — EFI NVRAM variables are not portable across hypervisors")
        elif re.match(r"^(virtio|scsi|sata|ide)\d+$", key):
            if "media=cdrom" not in val:
                m = re.match(r"(?:file=)?([^:,\s]+:[^,\s]+)(?:,|$)", val)
                if m:
                    cfg["disks"].append(m.group(1))

    cfg["vcpus"] = cfg["cores"] * cfg["sockets"]
    return cfg


# ── OVF 1.0 ───────────────────────────────────────────────────────────────────

def _ovf(name: str, vcpus: int, memory: int, bios: str, disks: list[dict], networks: list[str]) -> bytes:
    refs = "\n".join(
        f'    <File ovf:id="file{i}" ovf:href="{d["name"]}" ovf:size="{d["size"]}"/>'
        for i, d in enumerate(disks)
    )
    disk_elems = "\n".join(
        f'    <Disk ovf:diskId="disk{i}" ovf:fileRef="file{i}"'
        f' ovf:capacity="{d["vsize"]}" ovf:capacityAllocationUnits="byte"'
        f' ovf:format="http://www.vmware.com/interfaces/specifications/vmdk.html#streamOptimized"/>'
        for i, d in enumerate(disks)
    )
    # InstanceID 20+ avoids collision with controller (4) and NIC IDs (5+i)
    disk_items = "\n".join(
        f"      <Item>\n"
        f"        <rasd:AddressOnParent>{i}</rasd:AddressOnParent>\n"
        f"        <rasd:ElementName>disk{i}</rasd:ElementName>\n"
        f"        <rasd:HostResource>ovf:/disk/disk{i}</rasd:HostResource>\n"
        f"        <rasd:InstanceID>{20 + i}</rasd:InstanceID>\n"
        f"        <rasd:Parent>4</rasd:Parent>\n"
        f"        <rasd:ResourceType>17</rasd:ResourceType>\n"
        f"      </Item>"
        for i in range(len(disks))
    )

    net_names = networks if networks else ["VM Network"]
    unique_nets = list(dict.fromkeys(net_names))
    net_elems = "\n".join(
        f'    <Network ovf:name="{b}"><Description>Proxmox bridge: {b}</Description></Network>'
        for b in unique_nets
    )
    nic_items = "\n".join(
        f"      <Item>\n"
        f"        <rasd:AutomaticAllocation>true</rasd:AutomaticAllocation>\n"
        f"        <rasd:Connection>{bridge}</rasd:Connection>\n"
        f"        <rasd:ElementName>Network Adapter {i}</rasd:ElementName>\n"
        f"        <rasd:InstanceID>{5 + i}</rasd:InstanceID>\n"
        f"        <rasd:ResourceSubType>VmxNet3</rasd:ResourceSubType>\n"
        f"        <rasd:ResourceType>10</rasd:ResourceType>\n"
        f"      </Item>"
        for i, bridge in enumerate(net_names)
    )

    # VMware-specific firmware hint (ovf:required=false → ignored by other tools)
    efi_item = ('      <vmw:ExtraConfig ovf:required="false" vmw:key="firmware" vmw:value="efi"/>\n'
                if bios == "ovmf" else "")

    return f"""<?xml version="1.0" encoding="UTF-8"?>
<Envelope xmlns="http://schemas.dmtf.org/ovf/envelope/1"
  xmlns:ovf="http://schemas.dmtf.org/ovf/envelope/1"
  xmlns:rasd="http://schemas.dmtf.org/wbem/wscim/1/cim-schema/2/CIM_ResourceAllocationSettingData"
  xmlns:vmw="http://www.vmware.com/schema/ovf"
  xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance">
  <References>
{refs}
  </References>
  <DiskSection>
    <Info>Virtual disks</Info>
{disk_elems}
  </DiskSection>
  <NetworkSection>
    <Info>Virtual networks</Info>
{net_elems}
  </NetworkSection>
  <VirtualSystem ovf:id="{name}">
    <Info>{name}</Info><Name>{name}</Name>
    <OperatingSystemSection ovf:id="96">
      <Info>Guest OS</Info><Description>Debian GNU/Linux</Description>
    </OperatingSystemSection>
    <VirtualHardwareSection>
      <Info>Virtual hardware</Info>
      <System>
        <rasd:ElementName>Virtual Hardware Family</rasd:ElementName>
        <rasd:InstanceID>0</rasd:InstanceID>
        <rasd:VirtualSystemType>vmx-19</rasd:VirtualSystemType>
      </System>
      <Item>
        <rasd:AllocationUnits>hertz * 10^6</rasd:AllocationUnits>
        <rasd:ElementName>{vcpus} vCPU</rasd:ElementName>
        <rasd:InstanceID>1</rasd:InstanceID><rasd:ResourceType>3</rasd:ResourceType>
        <rasd:VirtualQuantity>{vcpus}</rasd:VirtualQuantity>
      </Item>
      <Item>
        <rasd:AllocationUnits>byte * 2^20</rasd:AllocationUnits>
        <rasd:ElementName>{memory} MB RAM</rasd:ElementName>
        <rasd:InstanceID>2</rasd:InstanceID><rasd:ResourceType>4</rasd:ResourceType>
        <rasd:VirtualQuantity>{memory}</rasd:VirtualQuantity>
      </Item>
      <Item>
        <rasd:Address>0</rasd:Address>
        <rasd:ElementName>SCSI Controller 0</rasd:ElementName>
        <rasd:InstanceID>4</rasd:InstanceID>
        <rasd:ResourceSubType>VirtualSCSI</rasd:ResourceSubType>
        <rasd:ResourceType>6</rasd:ResourceType>
      </Item>
{nic_items}
{disk_items}
{efi_item}    </VirtualHardwareSection>
  </VirtualSystem>
</Envelope>""".encode()


def _manifest(entries: list[tuple[str, str]]) -> bytes:
    """OVA manifest: SHA256(filename)= hexhash per line."""
    return "".join(f"SHA256({name})= {digest}\n" for name, digest in entries).encode()


# ── Verify ────────────────────────────────────────────────────────────────────

def _verify_vmdk(vmdk: Path) -> None:
    log.info("Verifying %s", vmdk.name)
    r = subprocess.run(["qemu-img", "check", str(vmdk)], capture_output=True, text=True)
    out = (r.stdout + r.stderr).strip()
    for line in out.splitlines():
        log.info("qemu-img: %s", line)
    if r.returncode != 0:
        raise SystemExit(f"VMDK check failed (rc={r.returncode}): {vmdk.name}\n{out}")
    log.info("OK: %s", vmdk.name)


# ── Progress ──────────────────────────────────────────────────────────────────

def _fmt_dur(s: float) -> str:
    s = int(s); h = s // 3600; m = (s % 3600) // 60; s = s % 60
    return f"{h}h {m:02d}m {s:02d}s" if h else (f"{m}m {s:02d}s" if m else f"{s}s")


def _make_progress(label: str, total: int, logical: bool = False) -> Callable[[int, int], None]:
    t0 = time.monotonic(); last_logged = [-1]; last_print = [0.0]

    def show(done: int, _total: int) -> None:
        now = time.monotonic(); dt = now - t0
        if now - last_print[0] < 1.0 and done < _total:
            return
        last_print[0] = now
        pct = done * 100 // _total if _total else 0
        if dt > 0:
            speed = done / dt / (1 << 20)
            eta   = _fmt_dur((_total - done) / (done / dt) if done else 0)
        else:
            speed = 0.0; eta = "--"
        unit = "logical MiB/s" if logical else "MiB/s"
        print(f"\r  {pct:3d}%  {done >> 20}/{_total >> 20} MiB"
              f"  {speed:.1f} {unit}  {_fmt_dur(dt)} elapsed  ETA {eta}   ",
              end="", flush=True)
        decile = pct // 10
        if decile != last_logged[0]:
            last_logged[0] = decile
            log.info("%s %d%%  %d/%d MiB  %.1f %s  %s elapsed  ETA %s",
                     label, pct, done >> 20, _total >> 20, speed, unit, _fmt_dur(dt), eta)
    return show


# ── main ──────────────────────────────────────────────────────────────────────

def _setup_logging(log_path: Path | None) -> None:
    fmt = logging.Formatter("%(asctime)s  %(levelname)-7s  %(message)s",
                            datefmt="%Y-%m-%d %H:%M:%S")
    if log_path is not None:
        fh = logging.FileHandler(log_path, encoding="utf-8")
        fh.setLevel(logging.DEBUG); fh.setFormatter(fmt); log.addHandler(fh)
        log.setLevel(logging.DEBUG)
    sh = logging.StreamHandler(sys.stderr)
    sh.setLevel(logging.WARNING); sh.setFormatter(fmt); log.addHandler(sh)
    if log_path is None:
        log.setLevel(logging.WARNING)


def main() -> None:
    ap = argparse.ArgumentParser(
        description="Export Proxmox VM to OVA — allocation-aware reads + parallel VMDK compression",
        epilog="Requires dmsetup and thin_dump (thin-provisioning-tools) by default. "
               "Keep the VM stopped and its disks unchanged throughout export: a metadata "
               "reservation is not a data snapshot or a write lock.")
    ap.add_argument("--vmid",    type=int,  required=True, metavar="ID",
                    help="Proxmox VM ID")
    ap.add_argument("--out",     type=Path, default=Path("/var/lib/vz/import"), metavar="DIR",
                    help="Output directory for final OVA (default: /var/lib/vz/import)")
    ap.add_argument("--tmp",     type=Path, default=None, metavar="DIR",
                    help="Directory for intermediate VMDKs (default: same as --out)")
    ap.add_argument("--name",    default="", metavar="NAME",
                    help="OVA base name (default: VM name)")
    ap.add_argument("--workers", type=int, default=min(32, os.cpu_count() or 4), metavar="N",
                    help="Parallel compression threads")
    ap.add_argument("--level",   type=int, default=6, choices=range(1, 10), metavar="1-9",
                    help="zlib compression level (1=fast/large … 9=slow/small, default=6)")
    ap.add_argument("--log",     type=Path, default=None, metavar="FILE",
                    help="Append detailed log to FILE")
    ap.add_argument("--verify",  action="store_true",
                    help="Run qemu-img check on each VMDK after conversion")
    ap.add_argument("--no-thin-map", action="store_true",
                    help="Read the full device without thin metadata (explicit fallback); "
                         "zero grains are still omitted")
    args = ap.parse_args()
    if args.workers < 1:
        ap.error("--workers must be positive")

    _setup_logging(args.log)

    if os.geteuid() != 0:
        raise SystemExit("Must run as root")
    if _vm_status(args.vmid) != "stopped":
        raise SystemExit(f"VM {args.vmid} must be stopped before export")

    cfg = _vm_config(args.vmid)
    if not cfg["disks"]:
        raise SystemExit("No exportable disks found in VM config")
    _check_disk_storages(cfg["disks"])

    if cfg["scsihw"].startswith("virtio"):
        msg = (f"WARNING: VM uses '{cfg['scsihw']}' — after import on Proxmox "
               f"change SCSI controller to 'VirtIO SCSI' in Hardware settings")
        print(msg)
        log.warning(msg)

    name = args.name or cfg["name"]
    if args.tmp is None:
        args.tmp = args.out
    args.out.mkdir(parents=True, exist_ok=True)
    args.tmp.mkdir(parents=True, exist_ok=True)
    ova_path = args.out / f"{name}.ova"

    print(f"\n{'='*60}")
    print(f"  VM {args.vmid} — {name}  ({cfg['vcpus']} vCPU, {cfg['memory']} MB, bios={cfg['bios']})")
    print(f"  Disks   : {' '.join(cfg['disks'])}")
    print(f"  Networks: {' '.join(cfg['networks']) or '(none detected)'}")
    print(f"  Output  : {ova_path}")
    print(f"  Workers : {args.workers}  level {args.level}  verify {'yes' if args.verify else 'no'}")
    print(f"{'='*60}\n")
    log.info("Export VM %d (%s) disks=%s workers=%d verify=%s",
             args.vmid, name, cfg["disks"], args.workers, args.verify)

    vmdk_paths: list[Path] = []

    def _cleanup() -> None:
        for p in vmdk_paths:
            p.unlink(missing_ok=True)

    def _interrupt(sig, _frame) -> None:
        log.warning("Interrupted (signal %s)", sig)
        raise SystemExit(f"Interrupted (signal {sig})")

    previous_handlers = {sig: signal.signal(sig, _interrupt)
                         for sig in (signal.SIGINT, signal.SIGTERM)}
    t_start = time.monotonic()

    try:
        if not args.no_thin_map:
            _check_thin_tools()
        disk_meta   = []
        vmdk_hashes = []  # (filename, sha256) collected during conversion for .mf

        for i, lv in enumerate(cfg["disks"]):
            vmdk    = args.tmp / f"{name}-disk{i}.vmdk"
            lv_path = _run("pvesm", "path", lv).stdout.strip()
            vmdk_paths.append(vmdk)

            print(f"[{i}] {lv}  →  {vmdk.name}")
            log.info("[disk %d] %s → %s", i, lv, vmdk.name)
            t_disk = time.monotonic()
            try:
                _lv("y", lv_path)
                vsize = _source_size(lv_path)
                if _vm_status(args.vmid) != "stopped":
                    raise RuntimeError(f"VM {args.vmid} must remain stopped; refusing map capture")
                mapped_ranges = None if args.no_thin_map else _thin_map(lv_path, vsize)
                mapped_bytes = (vsize if mapped_ranges is None else
                                sum(end - start for start, end in mapped_ranges))
                summary = (f"Logical size: {vsize} bytes; "
                           f"{'full-device' if mapped_ranges is None else 'mapped'} bytes to read: "
                           f"{mapped_bytes}; skipped: {vsize - mapped_bytes} bytes")
                print(f"  {summary}")
                log.info("[disk %d] %s", i, summary)
                vmdk_sha = VmdkWriter(
                    src=lv_path, dst=vmdk, workers=args.workers, level=args.level,
                    on_progress=_make_progress(f"disk{i}", vsize, logical=True),
                    mapped_ranges=mapped_ranges, src_size=vsize,
                ).convert()
                if _vm_status(args.vmid) != "stopped":
                    raise RuntimeError(f"VM {args.vmid} did not remain stopped; discarding export")
            finally:
                _lv("n", lv_path)

            elapsed   = time.monotonic() - t_disk
            vmdk_size = vmdk.stat().st_size
            print(f"\n  → {vmdk.name}  {vmdk_size >> 20} MiB"
                  f"  ({_fmt_dur(elapsed)}, {vsize / elapsed / (1 << 20):.1f} logical MiB/s)")
            log.info("[disk %d] done: %d MiB → %d MiB in %s",
                     i, vsize >> 20, vmdk_size >> 20, _fmt_dur(elapsed))

            if args.verify:
                print(f"  Verify {vmdk.name}...")
                _verify_vmdk(vmdk)
                print("  OK")

            disk_meta.append({"name": vmdk.name, "size": vmdk_size, "vsize": vsize})
            vmdk_hashes.append((vmdk.name, vmdk_sha))

        # Pack OVA: OVF → MF → VMDKs (manifest must precede disk files per OVF spec)
        ovf_data = _ovf(name, cfg["vcpus"], cfg["memory"], cfg["bios"], disk_meta, cfg["networks"])
        mf_data  = _manifest(
            [(f"{name}.ovf", hashlib.sha256(ovf_data).hexdigest())] + vmdk_hashes
        )

        print("\nPacking OVA (hole-punch streaming)...")
        log.info("Packing OVA: %s", ova_path)
        t_pack = time.monotonic()
        with OvaWriter(ova_path) as ova:
            ova.add_bytes(f"{name}.ovf", ovf_data)
            ova.add_bytes(f"{name}.mf",  mf_data)
            for vmdk in list(vmdk_paths):
                sz = vmdk.stat().st_size
                print(f"  {vmdk.name}  ({sz >> 20} MiB)")
                log.info("Packing %s (%d MiB)", vmdk.name, sz >> 20)
                t0 = time.monotonic()
                ova.add_file(vmdk.name, vmdk, on_progress=_make_progress(f"pack:{vmdk.stem}", sz))
                pack_t = time.monotonic() - t0
                print(f"\n  → packed {_fmt_dur(pack_t)}  ({sz / pack_t / (1 << 20):.1f} MiB/s)")
                log.info("Packed %s in %s", vmdk.name, _fmt_dur(pack_t))
                vmdk_paths.remove(vmdk)

        log.info("OVA packed in %s", _fmt_dur(time.monotonic() - t_pack))

    except Exception as exc:
        log.error("Fatal: %s", exc, exc_info=True)
        raise SystemExit(f"Error: {exc}") from exc
    finally:
        try:
            _cleanup()
        finally:
            for sig, handler in previous_handlers.items():
                signal.signal(sig, handler)

    elapsed = time.monotonic() - t_start
    gb      = ova_path.stat().st_size / 1024 ** 3
    print(f"\n{'='*60}")
    print(f"  {ova_path.name}  ({gb:.2f} GB)  {elapsed / 60:.1f} min")
    print(f"{'='*60}\n")
    log.info("Done: %s (%.2f GB) in %.1f min", ova_path.name, gb, elapsed / 60)


if __name__ == "__main__":
    main()
