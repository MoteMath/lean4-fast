#!/usr/bin/env python3
"""
Generate corrupted .olean fixtures from a valid DownstreamBench/Prelude.olean
for Gate 2 negative soundness verification.
"""
from pathlib import Path
import sys

SRC = Path(__file__).resolve().parent / "downstream_bench" / ".lake" / "build" / "lib" / "lean" / "DownstreamBench" / "Prelude.olean"
OUT = Path(__file__).resolve().parent / "corrupt_oleans"

if not SRC.exists():
    print(f"Missing source olean: {SRC}", file=sys.stderr)
    sys.exit(1)

OUT.mkdir(parents=True, exist_ok=True)
data = bytearray(SRC.read_bytes())

# 1. Corrupt header magic
d1 = bytearray(data)
d1[0:5] = b"BADOL"
(OUT / "bad_magic.olean").write_bytes(d1)

# 2. Truncated olean
(OUT / "truncated.olean").write_bytes(data[: max(16, len(data) // 2)])

# 3. Corrupt base/root pointer near header (offset 64..72)
d3 = bytearray(data)
for i in range(64, min(72, len(d3))):
    d3[i] ^= 0xFF
(OUT / "corrupt_header_ptr.olean").write_bytes(d3)

# 4. Corrupt payload region near middle
d4 = bytearray(data)
mid = len(d4) // 2
for i in range(mid, min(mid + 32, len(d4))):
    d4[i] ^= 0xA5
(OUT / "corrupt_payload.olean").write_bytes(d4)

print(f"Generated 4 corrupt .olean fixtures from {SRC} ({len(data)} bytes) in {OUT}")
