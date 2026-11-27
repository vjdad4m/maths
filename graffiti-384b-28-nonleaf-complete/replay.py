"""Strictly replay the complete 29-type, 28-nonleaf theorem for Graffiti.pc 384b."""
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
ARCHIVES = {'graff384b-sparsecontact28-sources.zip': '2c3d70a67117e4f8ccd543dbc119aafd72e8486ec91fad3f8c93b51da4036a0d'}
MATHLIB = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
NEW = ['FiveCommonGeometry28', 'FiveCommonSaving28', 'SixGeometry28', 'SixRows28', 'MixedTrials28', 'BoardBudget28', 'RankBoard28', 'DisjointFinish28', 'FinishNonleaves28']

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
    ordered = {}
    def visit(name):
        if name in ordered:
            return
        assert name in files and len(files[name]) == 1, name
        data = next(iter(files[name].values()))
        for dep in re.findall(r"^import ([^\s]+)", data.decode(), re.M):
            if dep in files:
                visit(dep)
            else:
                assert dep.split(".")[0] in ("Mathlib", "Std", "Init", "Lean", "Batteries"), dep
        ordered[name] = data
    for name in ("FrontierTwentyNine384b", "ThirtyBoth31", "RankTable384b", "ShoreEquality28", "ShoreSample28", "ShoreSplitBudget28", "ShoreFinish28", "CorePalette28", "CoreFrontier28", "ProtectedFiber28", "ProtectedPair28", "SharedFrontier28")+tuple(['FourPool28', 'FourCharges28', 'FourLocal28', 'FourDiamond28', 'FourFan28', 'FourWheel28', 'FourEar28', 'FourSquareSample28', 'FourPairRebate28', 'FourPairSample28', 'FourSquareSaving28', 'FourLowSquare28', 'FourQuartic28', 'FourFrontier28'])+tuple(['QuarticCredits28', 'QuarticContact28', 'QuarticFinish28', 'ThinTable28', 'ThinTrial28', 'ThinCharges28', 'ThinFinish28', 'SquareResidual28'])+tuple(['HighTable28', 'HighBasics28', 'HighTrial28', 'HighEndpoint28', 'SinglePrice28', 'SingleFinish28', 'HighFrontier28', 'PortFibers28', 'PortGeometry28', 'PortBudget28', 'PortRepair28', 'PortSaving28', 'HighDisjoint28', 'OddSquare28', 'MatchedSquare28'])+tuple(['SparseLink28', 'FrameLinks28', 'WeightedRows28', 'ThreeTrials28', 'CliqueForced28', 'OriginalClique28']):
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
    stage = Path(tempfile.mkdtemp(prefix=".fivefinish28.", dir=HERE))
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
    print("Full-28 replay", stage, flush=True)
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
        print(f"Matched the frozen sparse-28 archive, {len(ordered)} source hashes and {len(ordered)} predecessor objects.", flush=True)
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
