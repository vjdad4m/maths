import json
import re
import sys
from pathlib import Path

root = Path(__file__).resolve().parent
dst = Path(sys.argv[1])
dst.mkdir(parents=True, exist_ok=True)
data = json.loads((root / "finite_sources.json").read_text())
assert len(data["files"]) == len(data["order"]) == 15
for name in data["order"]:
    assert re.fullmatch(r"OffFiveConnectedTwin[A-Za-z0-9_]+\.lean", name)
    (dst / name).write_text(data["files"][name])
    print(name.removesuffix(".lean"))
