import json
import re
import sys
from pathlib import Path

here = Path(__file__).resolve().parent
dst = Path(sys.argv[1])
dst.mkdir(parents=True, exist_ok=True)
data = json.loads((here / "solo_parts.json").read_text())
assert len(data["parts"]) == 49 and len(data["rows"]) == 16
for part in data["parts"]:
    name = "Solo_" + re.search(r"theorem (part_\d+_\d+_\d+_\d+)", part)[1]
    (dst / (name + ".lean")).write_text(
        "import SoloFastBaseVerified\n\nnamespace OffFour16Solo\n"
        + part + "\nend OffFour16Solo\n"
    )
    print(name)
for key, row in data["rows"].items():
    name = "Solo_row_" + key
    imports = "".join("import Solo_" + k + "\n" for k in re.findall(r"part_\d+_\d+_\d+_\d+", row))
    (dst / (name + ".lean")).write_text(
        "import SoloFastBaseVerified\n" + imports
        + "\nnamespace OffFour16Solo\n" + row + "\nend OffFour16Solo\n"
    )
    print(name)
