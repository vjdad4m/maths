"""Strictly replay the complete 29-type, 30-nonleaf theorem for Graffiti.pc 384b."""
import argparse
import hashlib
import io
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
from zipfile import ZipFile

HERE = Path(__file__).resolve().parent
ARCHIVES = {'graff384b-fivefinish28-sources.zip': 'f792ffa941548086db862e718a624d5dc14bc322d929449448ac0ef2a85ebebf', 'shared-anchors-source.zip': 'c639bb3009e19285ad2e167e6fa53bbc756cc1b9a1335942ecc5258522317111'}
MATHLIB = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
NEW = ['EarMixtureRows', 'SimplicialCredit30', 'EarLayout30', 'EarFiber30', 'EarTotal30', 'SixAnchorSaving30', 'OriginalSix30']

def digest(data):
    return hashlib.sha256(data).hexdigest()

def source_map():
    seen, files = set(), {}
    def unpack(raw):
        sha = digest(raw)
        if sha in seen:
            return
        seen.add(sha)
        with ZipFile(io.BytesIO(raw)) as archive:
            assert archive.testzip() is None
            for path in archive.namelist():
                if path.endswith(".zip"):
                    unpack(archive.read(path))
                if path.endswith(".lean"):
                    name = Path(path).stem
                    data = archive.read(path)
                    files.setdefault(name, {})[digest(data)] = data
    for name, expected in ARCHIVES.items():
        raw = (HERE / name).read_bytes()
        assert digest(raw) == expected, name
        unpack(raw)
    return files

def baseline():
    files = source_map()
    preferred = {'ThirdEar': '4033dffbf289ab006032d0d31b94a5845076ff178db77209cebe5076abc46f5c', 'AnchorScores': '5d9d7261c1e5ee3ee382de0bec72e5fd74bea90ecda52f11ab25d481a61c82dd'}
    ordered = {}
    def visit(name):
        if name in ordered:
            return
        assert name in files, name
        if len(files[name]) > 1:
            data = files[name][preferred[name]]
        else:
            data = next(iter(files[name].values()))
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
    stage = Path(tempfile.mkdtemp(prefix=".sixanchor30.", dir=HERE))
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
    print("Six-anchor replay", stage, flush=True)
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
        print(f"Matched both frozen source archives, {len(ordered)} source hashes and {len(ordered)} predecessor objects.", flush=True)
    else:
        for k, data in ordered.items():
            compile_module(k, data, stage, env, lean, False)
        print(f"Rebuilt {len(ordered)} predecessor modules from the frozen source archives.", flush=True)
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
