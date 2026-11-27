"""Replay the published 138-module base and the new four-anchor results from source."""
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import time

from crossfour_lowerprofiles import split_table

here = Path(__file__).resolve().parent
upstream = here / "upstream-order34"
manifest = (upstream / "sha256sums.txt").read_bytes()
module_list = (upstream / "modules.txt").read_bytes()
sha = lambda contents: hashlib.sha256(contents).hexdigest()
assert sha(manifest) == "a8eb76f8c27ccf907eb1a19171d5a78293f8635c168086cead230544487bc78c"
assert sha(module_list) == "0f780a1a168faace13a7d946ad323be6fa6ee92d6ce48804b38403d91dd551b1"
modules = module_list.decode().splitlines()
sources = {name: upstream / (name + ".lean") for name in modules}
for line in manifest.decode().splitlines():
    digest, name = line.split()
    assert sha((upstream / name).read_bytes()) == digest, name
for name in ("Table", "Ranks", "Loss", "Frame", "Pins", "Triangle", "Path", "PendantLink", "Pendant", ""):
    module = "CrossFour" + name + "34_384b"
    sources[module] = here / (module + ".lean")

leanbin = Path(os.environ["CROSSFOUR_LEAN_BIN"]).resolve()
mathlib = Path(os.environ["CROSSFOUR_MATHLIB"]).resolve()
version = subprocess.check_output([leanbin / "lean", "--version"], text=True).strip()
assert "version 4.19.0," in version
assert (mathlib / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.19.0"
if (mathlib / ".git").exists():
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=mathlib, text=True).strip() == "c44e0c8ee63ca166450922a373c7409c5d26b00b"
env = dict(os.environ, PATH=str(leanbin) + ":" + os.environ["PATH"], MALLOC_ARENA_MAX="2")
paths = subprocess.check_output([leanbin / "lake", "env", "printenv", "LEAN_PATH"], cwd=mathlib, env=env, text=True).strip().split(":")
if not sys.argv[1:]:
    build = Path(tempfile.mkdtemp(prefix=".crossfour34.", dir=here))
elif len(sys.argv) == 3 and sys.argv[1] == "--resume" and re.fullmatch(r"[.]crossfour34[.][a-zA-Z0-9_]{8}", sys.argv[2]):
    build = here / sys.argv[2]
    assert build.is_dir() and not build.is_symlink()
else:
    raise SystemExit("Usage: verify-crossfour34.sh [--resume .crossfour34.XXXXXXXX]")
env["LEAN_PATH"] = ":".join(map(str, [build] + [(mathlib / path).resolve() for path in paths]))
fingerprint = {m: sha(path.read_bytes()) for m, path in sources.items()}
fingerprint.update({p.name: sha(p.read_bytes()) for p in (Path(__file__), here / "crossfour_lowerprofiles.py")})
tag = build / "sources.json"
if tag.exists():
    assert json.loads(tag.read_text()) == fingerprint, "Sources changed since the interrupted run"
else:
    assert not list(build.glob("*.olean"))
    tag.write_text(json.dumps(fingerprint, sort_keys=True))
print(version, flush=True)
print(f"Verified {len(modules)} published source hashes. Build directory {build.name}", flush=True)
allowed = {"propext", "Quot.sound", "Classical.choice"}
audit = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")
checked = 0
for name, source in sources.items():
    obj = build / (name + ".olean")
    log = build / (name + ".log")
    if not (obj.is_file() and log.is_file()):
        original = source.read_text()
        for attempt in range(3):
            current = source
            split = split_table(name, original) if attempt or name == "LowerProfiles384b" else None
            if split is not None:
                scratch = build / "split"
                scratch.mkdir(exist_ok=True)
                current = scratch / source.name
                current.write_text(split)
            run = subprocess.run([leanbin / "lean", "-j1", "-s", "65536", "-DElab.async=false",
                                  "-DwarningAsError=true", "-o", obj, current.name],
                                 cwd=current.parent, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if run.returncode == 0:
                log.write_text(run.stdout)
                break
            obj.unlink(missing_ok=True)
            print(run.stdout, end="", flush=True)
            if run.returncode != -signal.SIGKILL or attempt == 2:
                run.check_returncode()
            print(f"Retrying interrupted compiler for {name}.", flush=True)
            time.sleep(5)
    result = log.read_text()
    print(result, end="", flush=True)
    assert not re.search(r"\b(?:error|warning):|\bsorryAx\b", result), name
    found = []
    for line in result.splitlines():
        if "depends on axioms" in line:
            a = audit.fullmatch(line)
            assert a and set(a[2].split(", ")) <= allowed, line
            found.append(a[1])
        elif "does not depend on any axioms" in line:
            found.append(line.split("'")[1])
    expected = re.findall(r"^#print axioms ([.\w]+)\s*$", source.read_text(), re.MULTILINE)
    assert sorted(expected) == sorted(found), (name, expected, found)
    checked += len(found)
print(f"Complete order-34 four-anchor replay passed ({len(sources)} modules, {checked} axiom reports).", flush=True)

