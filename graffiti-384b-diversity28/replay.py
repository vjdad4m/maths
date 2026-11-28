"""Strictly replay the all-order 28-type theorem for Graffiti.pc 384b."""
import argparse
import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
MATHLIB = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
NEW = ['TenSeeds28', 'EarCredit28', 'RankBudgetTypes28', 'DiversityTwentyEight384b']

def digest(data):
    return hashlib.sha256(data).hexdigest()

def baseline():
    files = {p.stem: p.read_bytes() for p in (HERE / "prior").glob("*.lean")}
    ordered = {}
    def visit(name):
        if name in ordered:
            return
        assert name in files, name
        data = files[name]
        for dep in re.findall(r"^import ([^\s]+)", data.decode(), re.M):
            if dep in files:
                visit(dep)
            else:
                assert dep.split(".")[0] in ("Mathlib", "Std", "Init", "Lean", "Batteries"), dep
        ordered[name] = data
    for fresh in NEW:
        for name in re.findall(r"^import ([^\s]+)", (HERE / (fresh+".lean")).read_text(), re.M):
            if name not in NEW:
                visit(name)
    assert set(ordered) == set(files)
    return ordered

def manifest(path):
    return {name: sha for sha, name in (row.split() for row in path.read_text().splitlines())}

def compile_module(name, data, stage, env, lean, new):
    source = stage / (name + ".lean")
    source.write_bytes(data)
    if new:
        assert not re.search(rb"\b(?:sorry|admit|axiom|native_decide)\b", data), name
    target = stage / "build" / (name + ".olean")
    proc = subprocess.run([lean / "lean", "-j1", "-s", "65536", "-DElab.async=false",
                           "-DwarningAsError=true", "-o", target, source.name], cwd=stage,
                          env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (stage / (name + ".log")).write_text(proc.stdout)
    print(proc.stdout, end="", flush=True)
    proc.check_returncode()
    assert target.stat().st_size
    assert not re.search(r"\b(?:error|warning):|sorryAx", proc.stdout), name
    reports = re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", proc.stdout, re.M)
    if new:
        declared = re.findall(rb"^#print axioms ([\w.]+)$", data, re.M)
        assert [x.decode() for x in declared] == [theorem for theorem, _ in reports], name
        assert declared
    for theorem, dep in reports:
        assert set(dep.split(", ")) <= ALLOWED, theorem
    return len(reports)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--cold", action="store_true", help="compile the transitive predecessor sources (default)")
    modes.add_argument("--checked", metavar="WORKSPACE", type=Path, help="load the hash-matched predecessor objects in the recorded workspace")
    args = parser.parse_args()
    stage = Path(tempfile.mkdtemp(prefix=".types28.", dir=HERE))
    (stage / "build").mkdir()
    (stage / "prior").mkdir()
    env = os.environ.copy()
    deps = HERE.parent / "graff384b-codex/.deps"
    lean = Path(env.get("CROSSFOUR_LEAN_BIN", deps / "lean-4.19.0-linux/bin")).resolve()
    ml = Path(env.get("CROSSFOUR_MATHLIB", deps / "mathlib4")).resolve()
    env["PATH"] = str(lean) + os.pathsep + env["PATH"]
    ver = subprocess.check_output([lean / "lean", "--version"], text=True).strip()
    assert "version 4.19.0," in ver and "commit 6caaee842e94," in ver
    assert subprocess.check_output(["git", "-C", ml, "rev-parse", "HEAD"], text=True).strip() == MATHLIB
    lib = subprocess.check_output([lean / "lake", "env", "printenv", "LEAN_PATH"], env=env, cwd=ml, text=True).strip()
    env["LEAN_PATH"] = os.pathsep.join(map(str, [stage/"build", stage/"prior"] + [(ml/p).resolve() for p in lib.split(os.pathsep)]))
    print("Diversity-28 replay", stage, flush=True)
    print(ver, flush=True)
    print("Mathlib", MATHLIB, flush=True)
    ordered = baseline()
    hashes = manifest(HERE/"PRIOR-SOURCES.sha256")
    assert list(hashes) == [k+".lean" for k in ordered]
    assert all(digest(data) == hashes[k+".lean"] for k, data in ordered.items())
    assert all(not re.search(rb"\b(?:sorry|admit|axiom|native_decide)\b", data) for data in ordered.values())
    locations = {}
    for line in (HERE/"CHECKED-OBJECTS.tsv").read_text().splitlines():
        name, sha, rel = line.split("\t")
        assert not Path(rel).is_absolute() and ".." not in Path(rel).parts
        locations[name] = (sha, rel)
    assert set(locations) == set(ordered)
    if args.checked:
        for k, (sha, rel) in locations.items():
            path = args.checked / rel
            assert digest(path.read_bytes()) == sha, path
            target = stage/"prior"/(k+".olean")
            try:
                os.link(path, target)
            except OSError:
                shutil.copy2(path, target)
        print(f"Matched {len(ordered)} source hashes and {len(ordered)} predecessor objects.", flush=True)
    else:
        for k, data in ordered.items():
            compile_module(k, data, stage, env, lean, False)
        print(f"Rebuilt {len(ordered)} predecessor modules from the bundled sources.", flush=True)
    new_hashes = manifest(HERE/"NEW-SOURCES.sha256")
    assert list(new_hashes) == [name+".lean" for name in NEW]
    nr = 0
    for k in NEW:
        raw = (HERE/(k+".lean")).read_bytes()
        assert digest(raw) == new_hashes[k+".lean"]
        nr += compile_module(k, raw, stage, env, lean, True)
    assert nr == sum(len(re.findall(r'^#print axioms ', (HERE/(name+'.lean')).read_text(), re.M)) for name in NEW)
    expected = manifest(HERE/'NEW-OBJECTS.sha256')
    assert list(expected) == [k+'.olean' for k in NEW]
    for name, sha in expected.items():
        assert digest((stage/'build'/name).read_bytes()) == sha, name
    print(f'Matched all {len(expected)} fresh object hashes.', flush=True)
    print(f"Verified {len(NEW)} fresh modules and {nr} standard-axiom reports.", flush=True)

if __name__ == "__main__":
    main()
