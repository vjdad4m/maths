"""Check the five public theorem reports and the freshly checked sources."""
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parent
stage = Path(sys.argv[1])
for stem, count in [("PendantSample", 2), ("PendantBound", 3)]:
    source = (stage / (stem + ".lean")).read_bytes()
    assert source == (root / (stem + ".lean")).read_bytes()
    assert not re.search(rb"\b(?:sorry|admit|axiom|native_decide)\b", source)
    expected = re.findall(r"^#print axioms ([\w.]+)$", source.decode(), re.M)
    output = (stage / (stem + ".log")).read_text()
    assert len(expected) == len(set(expected)) == count
    assert not re.search(r"\b(?:error|warning):|sorryAx", output)
    observed = re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", output, re.M)
    assert [name for name, _ in observed] == expected
    assert all(set(axioms.split(", ")) <= {"propext", "Classical.choice", "Quot.sound"}
               for _, axioms in observed)
    assert (stage / "build" / (stem + ".olean")).stat().st_size > 0
print("Pendant-triangle extension verified: 2 modules, 5 standard-axiom reports.")
