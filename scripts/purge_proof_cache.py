#!/usr/bin/env python3

"""Remove unrecognized values from a GNATprove memcached proof cache.

The cache currently has no key namespace, so every bare 40-character SHA-1
key (used by SPARK 26.2 and earlier) or 64-character Blake3 key is fetched and
its value is classified.  Recognized gnatwhy3 JSON results are retained without
inspecting their nested proof attempts.  For automatic provers, recognized
answer and step-limit lines are retained; everything else is a deletion
candidate.

Recognizing any answer line retains the complete value, including output that
the prover might have printed after that answer.  This follows the proposed
wrapper allowlist, but is not a full parse of the prover output.

This is a one-shot stopgap: unfixed producers can repopulate rejected entries.
Also, lru_crawler metadump is a best-effort live traversal, not an atomic
inventory, so a run may miss entries moving or arriving during the scan.

The default mode is a dry run.  Pass --delete explicitly to remove candidates.
"""

import argparse
import json
import re
import socket
import struct
import sys
import tempfile
from dataclasses import dataclass
from typing import BinaryIO, Iterator, Optional


MAX_RESPONSE_LINE = 64 * 1024
MAX_BATCH_SIZE = 1024
DEFAULT_PREVIEW_BYTES = 160
DEFAULT_MAX_DELETIONS = 1000
DEFAULT_MAX_CANDIDATE_RATIO = 0.05

CACHE_KEY = re.compile(rb"^(?:[0-9A-Fa-f]{40}|[0-9A-Fa-f]{64})$")

SMT_ANSWERS = {b"unsat", b"sat", b"unknown", b"Fail"}
SMT_REASON_UNKNOWN = re.compile(rb"^\(:reason-unknown [^)]*\)$")
STEP_LIMIT_ANSWERS = {
    b"(Step limit reached)",
    b"steplimitreached",
    b"unknown (RESOURCEOUT)",
}
ALT_ERGO_ANSWER = re.compile(
    rb'^(?:; )?File ".*", line [0-9]+, characters [0-9]+-[0-9]+:'
    rb" ?(?:Valid|Invalid|I don't know)(?:$|[ (].*)"
)
ALT_ERGO_STEP_LIMIT = re.compile(
    rb"^\[Error\]; Fatal Error: Steps limit reached(?:$|: .*)"
)


class ProtocolError(RuntimeError):
    """Raised when memcached sends an unexpected response."""


@dataclass(frozen=True)
class CacheItem:
    key: bytes
    value: bytes
    cas: bytes


@dataclass
class Statistics:
    enumerated: int = 0
    eligible_keys: int = 0
    foreign_keys: int = 0
    fetched: int = 0
    fetch_missing: int = 0
    gnatwhy3: int = 0
    prover: int = 0
    candidates: int = 0
    deleted: int = 0
    delete_missing: int = 0
    changed: int = 0


class MemcachedConnection:
    """Small client for the memcached commands needed by this utility."""

    def __init__(self, host: str, port: int, timeout: float):
        self._socket = socket.create_connection((host, port), timeout=timeout)
        self._socket.settimeout(timeout)
        self._reader = self._socket.makefile("rb")

    def close(self) -> None:
        self._reader.close()
        self._socket.close()

    def __enter__(self):
        return self

    def __exit__(self, _exc_type, _exc_value, _traceback):
        self.close()

    def send(self, data: bytes) -> None:
        self._socket.sendall(data)

    def read_line(self) -> bytes:
        line = self._reader.readline(MAX_RESPONSE_LINE + 1)
        if not line:
            raise ProtocolError("memcached closed the connection")
        if len(line) > MAX_RESPONSE_LINE:
            raise ProtocolError("memcached response line is too long")
        if not line.endswith(b"\n"):
            raise ProtocolError("unterminated memcached response line")
        return line.rstrip(b"\r\n")

    def read_exactly(self, size: int) -> bytes:
        chunks = []
        remaining = size
        while remaining:
            chunk = self._reader.read(remaining)
            if not chunk:
                raise ProtocolError("memcached closed the connection in a value")
            chunks.append(chunk)
            remaining -= len(chunk)
        return b"".join(chunks)

    def enumerate_keys(self, mode: str) -> Iterator[bytes]:
        self.send(f"lru_crawler metadump {mode}\r\n".encode("ascii"))
        while True:
            line = self.read_line()
            if line == b"END":
                return
            if line.startswith(
                (b"ERROR", b"CLIENT_ERROR", b"SERVER_ERROR", b"BUSY", b"BADCLASS")
            ):
                raise ProtocolError(line.decode("utf-8", "replace"))

            fields = {}
            for field in line.split(b" "):
                name, separator, value = field.partition(b"=")
                if separator:
                    fields[name] = value
            if b"key" not in fields:
                raise ProtocolError(
                    "metadump response has no key: " + line.decode("utf-8", "replace")
                )
            yield fields[b"key"]

    def request_items(self, keys: list[bytes]) -> Iterator[Optional[CacheItem]]:
        commands = []
        for number, key in enumerate(keys):
            commands.append(
                b"mg " + key + b" v c u O" + str(number).encode("ascii") + b"\r\n"
            )
        self.send(b"".join(commands))

        # Responses are consumed positionally.  Abort on an unexpected line;
        # continuing could associate every later response with the wrong key.
        for number, key in enumerate(keys):
            line = self.read_line()
            fields = line.split()
            if not fields:
                raise ProtocolError("empty meta-get response")

            if fields[0] == b"EN":
                yield None
                continue
            if fields[0] != b"VA" or len(fields) < 2:
                raise ProtocolError(line.decode("utf-8", "replace"))

            expected_opaque = b"O" + str(number).encode("ascii")
            if expected_opaque not in fields[2:]:
                raise ProtocolError("meta-get response has an unexpected opaque token")

            try:
                size = int(fields[1])
            except ValueError as exc:
                raise ProtocolError(
                    "invalid value length in meta-get response"
                ) from exc

            cas = next(
                (field[1:] for field in fields[2:] if field.startswith(b"c")), None
            )
            if cas is None or not cas.isdigit():
                raise ProtocolError("meta-get response has no valid CAS token")

            value = self.read_exactly(size)
            if self.read_exactly(2) != b"\r\n":
                raise ProtocolError("memcached value has no CRLF terminator")
            yield CacheItem(key=key, value=value, cas=cas)

    def delete_items(self, items: list[CacheItem]) -> Iterator[str]:
        commands = []
        for number, item in enumerate(items):
            commands.append(
                b"md "
                + item.key
                + b" C"
                + item.cas
                + b" O"
                + str(number).encode("ascii")
                + b"\r\n"
            )
        self.send(b"".join(commands))

        # As with meta-get, an unexpected response makes safe resynchronization
        # of this pipelined batch impossible.
        for number, _item in enumerate(items):
            line = self.read_line()
            fields = line.split()
            if not fields:
                raise ProtocolError("empty meta-delete response")

            if fields[0] == b"NF":
                yield "missing"
            elif fields[0] == b"EX":
                yield "changed"
            elif fields[0] != b"HD":
                raise ProtocolError(line.decode("utf-8", "replace"))
            else:
                expected_opaque = b"O" + str(number).encode("ascii")
                if expected_opaque not in fields[1:]:
                    raise ProtocolError(
                        "meta-delete response has an unexpected opaque token"
                    )
                yield "deleted"


def is_gnatwhy3_result(value: bytes) -> bool:
    """Recognize the normal and error forms of a gnatwhy3 JSON envelope."""

    try:
        document = json.loads(value)
    except (UnicodeDecodeError, json.JSONDecodeError):
        return False

    if not isinstance(document, dict) or not isinstance(document.get("results"), list):
        return False

    normal_result = type(document.get("entity")) is int and (
        "timings" not in document or isinstance(document["timings"], dict)
    )
    error_result = isinstance(document.get("error"), str) and (
        "internal" not in document or type(document["internal"]) is bool
    )
    return normal_result or error_result


def is_prover_result(value: bytes) -> bool:
    """Recognize a complete answer line from the supported automatic provers."""

    for line in value.replace(b"\r\n", b"\n").split(b"\n"):
        if (
            line in SMT_ANSWERS
            or line in STEP_LIMIT_ANSWERS
            or SMT_REASON_UNKNOWN.fullmatch(line) is not None
            or ALT_ERGO_ANSWER.fullmatch(line) is not None
            or ALT_ERGO_STEP_LIMIT.fullmatch(line) is not None
        ):
            return True
    return False


def classify(value: bytes) -> Optional[str]:
    if is_gnatwhy3_result(value):
        return "gnatwhy3"
    if is_prover_result(value):
        return "prover"
    return None


def printable_key(key: bytes) -> str:
    return key.decode("ascii")


def value_preview(value: bytes, limit: int) -> str:
    preview = repr(value[:limit])
    if len(value) > limit:
        preview += f"... (+{len(value) - limit} bytes)"
    return preview


def store_blob(stream: BinaryIO, blob: bytes) -> None:
    stream.write(struct.pack("!I", len(blob)))
    stream.write(blob)


def read_blob(stream: BinaryIO) -> Optional[bytes]:
    length_bytes = stream.read(4)
    if not length_bytes:
        return None
    if len(length_bytes) != 4:
        raise RuntimeError("truncated temporary cache record")
    length = struct.unpack("!I", length_bytes)[0]
    blob = stream.read(length)
    if len(blob) != length:
        raise RuntimeError("truncated temporary cache record")
    return blob


def key_batches(stream: BinaryIO, batch_size: int) -> Iterator[list[bytes]]:
    while True:
        batch = []
        while len(batch) < batch_size:
            key = read_blob(stream)
            if key is None:
                break
            batch.append(key)
        if not batch:
            return
        yield batch


def store_candidate(stream: BinaryIO, item: CacheItem) -> None:
    store_blob(stream, item.key)
    store_blob(stream, item.cas)


def candidate_batches(stream: BinaryIO, batch_size: int) -> Iterator[list[CacheItem]]:
    while True:
        batch = []
        while len(batch) < batch_size:
            key = read_blob(stream)
            if key is None:
                break
            cas = read_blob(stream)
            if cas is None:
                raise RuntimeError("truncated temporary candidate file")
            batch.append(CacheItem(key=key, value=b"", cas=cas))
        if not batch:
            return
        yield batch


def deletion_safety_error(
    stats: Statistics, max_deletions: int, max_candidate_ratio: float
) -> Optional[str]:
    if stats.candidates > max_deletions:
        return (
            f"refusing to delete {stats.candidates} candidates;"
            f" --max-deletions is {max_deletions}"
        )
    ratio = stats.candidates / stats.fetched if stats.fetched else 0.0
    if ratio > max_candidate_ratio:
        return (
            f"refusing to delete {stats.candidates}/{stats.fetched} fetched entries"
            f" ({ratio:.2%}); --max-candidate-ratio is"
            f" {max_candidate_ratio:.2%}"
        )
    return None


def scan(args: argparse.Namespace) -> tuple[Statistics, Optional[str]]:
    stats = Statistics()

    # Finish enumeration before fetching or deleting.  In particular, deletion
    # must not perturb the crawler that is producing the key list.
    with tempfile.TemporaryFile() as keys, tempfile.TemporaryFile() as candidates:
        with MemcachedConnection(args.host, args.port, args.timeout) as connection:
            for key in connection.enumerate_keys(args.metadump_mode):
                stats.enumerated += 1
                if CACHE_KEY.fullmatch(key) is None:
                    stats.foreign_keys += 1
                    if args.verbose:
                        print(f"skip foreign key={key!r}")
                    continue
                store_blob(keys, key)
                stats.eligible_keys += 1

        keys.seek(0)
        with MemcachedConnection(args.host, args.port, args.timeout) as connection:
            for batch in key_batches(keys, args.batch_size):
                for item in connection.request_items(batch):
                    if item is None:
                        stats.fetch_missing += 1
                        continue

                    stats.fetched += 1
                    kind = classify(item.value)
                    if kind == "gnatwhy3":
                        stats.gnatwhy3 += 1
                    elif kind == "prover":
                        stats.prover += 1
                    else:
                        stats.candidates += 1
                        store_candidate(candidates, item)
                        if not args.quiet:
                            action = "candidate" if args.delete else "would delete"
                            preview = (
                                ""
                                if args.preview_bytes == 0
                                else " value="
                                + value_preview(item.value, args.preview_bytes)
                            )
                            print(
                                f"{action} key={printable_key(item.key)}"
                                f" bytes={len(item.value)}{preview}"
                            )

                    if args.verbose and kind is not None:
                        print(
                            f"keep key={printable_key(item.key)}"
                            f" kind={kind} bytes={len(item.value)}"
                        )

        if not args.delete:
            return stats, None

        safety_error = deletion_safety_error(
            stats, args.max_deletions, args.max_candidate_ratio
        )
        if safety_error is not None:
            return stats, safety_error

        candidates.seek(0)
        with MemcachedConnection(args.host, args.port, args.timeout) as connection:
            for batch in candidate_batches(candidates, args.batch_size):
                for item, result in zip(
                    batch, connection.delete_items(batch), strict=True
                ):
                    if result == "deleted":
                        stats.deleted += 1
                    elif result == "missing":
                        stats.delete_missing += 1
                    else:
                        stats.changed += 1
                    if not args.quiet:
                        print(f"{result} key={printable_key(item.key)}")

    return stats, None


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--host", default="localhost", help="memcached host")
    parser.add_argument("--port", type=int, default=11211, help="memcached port")
    parser.add_argument(
        "--timeout", type=float, default=30.0, help="socket timeout in seconds"
    )
    parser.add_argument(
        "--batch-size",
        type=int,
        default=256,
        help=f"pipelined requests per batch, at most {MAX_BATCH_SIZE}",
    )
    parser.add_argument(
        "--metadump-mode",
        choices=("all", "hash"),
        default="all",
        help="metadump traversal mode (default: all)",
    )
    operation = parser.add_mutually_exclusive_group()
    operation.add_argument(
        "--dry-run",
        dest="delete",
        action="store_false",
        help="report deletion candidates without deleting them (default)",
    )
    operation.add_argument(
        "--delete",
        dest="delete",
        action="store_true",
        help="delete unrecognized values after safety checks",
    )
    parser.set_defaults(delete=False)
    parser.add_argument(
        "--preview-bytes",
        type=int,
        default=DEFAULT_PREVIEW_BYTES,
        help="candidate value bytes shown as repr; 0 hides values",
    )
    parser.add_argument(
        "--max-deletions",
        type=int,
        default=DEFAULT_MAX_DELETIONS,
        help="refuse --delete above this candidate count",
    )
    parser.add_argument(
        "--max-candidate-ratio",
        type=float,
        default=DEFAULT_MAX_CANDIDATE_RATIO,
        help="refuse --delete above this candidate/fetched ratio",
    )
    output = parser.add_mutually_exclusive_group()
    output.add_argument("--quiet", action="store_true", help="print only the summary")
    output.add_argument(
        "--verbose", action="store_true", help="also print retained entries"
    )
    args = parser.parse_args()
    if not 1 <= args.port <= 65535:
        parser.error("--port must be between 1 and 65535")
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    if not 1 <= args.batch_size <= MAX_BATCH_SIZE:
        parser.error(f"--batch-size must be between 1 and {MAX_BATCH_SIZE}")
    if args.preview_bytes < 0:
        parser.error("--preview-bytes must not be negative")
    if args.max_deletions < 0:
        parser.error("--max-deletions must not be negative")
    if not 0.0 <= args.max_candidate_ratio <= 1.0:
        parser.error("--max-candidate-ratio must be between 0 and 1")
    return args


def print_summary(stats: Statistics) -> None:
    print(
        "summary:"
        f" enumerated_best_effort={stats.enumerated}"
        f" eligible_keys={stats.eligible_keys}"
        f" skipped_foreign_keys={stats.foreign_keys}"
        f" fetched={stats.fetched}"
        f" fetch_missing={stats.fetch_missing}"
        f" kept_gnatwhy3={stats.gnatwhy3}"
        f" kept_prover={stats.prover}"
        f" candidates={stats.candidates}"
        f" deleted={stats.deleted}"
        f" delete_missing={stats.delete_missing}"
        f" changed_before_delete={stats.changed}",
        flush=True,
    )


def main() -> int:
    args = parse_arguments()
    operation = "DELETE" if args.delete else "DRY RUN"
    print(f"{operation}: scanning {args.host}:{args.port}", flush=True)

    try:
        stats, safety_error = scan(args)
    except (OSError, ProtocolError, RuntimeError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1

    print_summary(stats)
    if safety_error is not None:
        print(f"safety check failed: {safety_error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
