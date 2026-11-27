from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parent
objects = Path(sys.argv[1])
total = 0
reports = 0
allowed = {"propext", "Classical.choice", "Quot.sound"}
for line in (root / "modules.txt").read_text().splitlines():
    module, target = line.split()
    output = (objects / (module + ".log")).read_text()
    assert not re.search(r"warning:|error:|sorryAx", output, re.I)
    axioms = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]+)\]", output))
    assert target in axioms
    assert all({a.strip() for a in dependencies.split(",")} == allowed for dependencies in axioms.values())
    reports += len(axioms)
    accepted = re.search(r"Kernel replay accepted (\d+) declarations including " + re.escape(target) + r"\.", output)
    assert accepted
    total += int(accepted.group(1))
print(f"{total} new declarations passed kernel replay. All {reports} printed axiom reports use exactly propext, Classical.choice and Quot.sound.")
