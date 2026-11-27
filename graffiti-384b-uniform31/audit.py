"""Verify each new Lean source, compiled object and all public theorem reports."""
import hashlib
import re
import sys
from pathlib import Path

here = Path(__file__).resolve().parent
build = Path(sys.argv[1])
lines = (here / "NEW-SOURCES.sha256").read_text().splitlines()
assert len(lines) == 6
for count, line in zip([2, 3, 1, 1, 1, 3], lines):
    digest, name = line.split()
    stem = Path(name).stem
    source = (build / name).read_bytes()
    assert source == (here / name).read_bytes() and hashlib.sha256(source).hexdigest() == digest
    assert not re.search(rb"\b(?:sorry|admit|axiom|native_decide)\b", source)
    expected = re.findall(r"^#print axioms ([\w.]+)$", source.decode(), re.M)
    assert len(set(expected)) == len(expected) == count
    out = (build / (stem + ".log")).read_text()
    assert not re.search(r"\b(?:error|warning):|sorryAx", out)
    reports = re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", out, re.M)
    assert [name for name, _ in reports] == expected
    assert all(set(a.split(", ")) <= {"Classical.choice", "Quot.sound", "propext"} for _, a in reports)
    assert (build / "build" / (stem + ".olean")).stat().st_size > 0
print("Fresh extension verified: 6 modules and 11 standard-axiom reports.")
