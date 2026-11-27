"""Replay the full pendant and low-mate proof over the frozen pendant-rank baseline."""
import argparse
import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from zipfile import ZipFile

HERE = Path(__file__).resolve().parent
PREVIOUS = "pendant-ranks-source.zip"
ARCHIVE_SHA = "2390d79145b03f248ff1072d59fea952db1537a2bf15f5c9243335c47de6d1bd"
MATHLIB = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
SOURCES = {
    "PoolCut": 1,
    "PoolFive": 1,
    "PoolRank": 1,
    "LowMateClose": 3,
}
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_manifest(path, root):
    names = []
    for line in path.read_text().splitlines():
        expected, name = line.split()
        assert digest(root / name) == expected, name
        names.append(name)
    return names


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--cold", action="store_true", help="rebuild the predecessor from its sources (default)")
    modes.add_argument("--checked", metavar="LOG", type=Path, help="use the original frozen pendant-rank replay and its checked objects")
    args = parser.parse_args()
    stage = Path(tempfile.mkdtemp(prefix=".pendant-close.", dir=HERE))
    print("Pendant-closure replay", stage, flush=True)
    env = os.environ.copy()
    fallback = HERE.parent / "graff384b-codex/.deps"
    lean = Path(env.get("CROSSFOUR_LEAN_BIN", fallback / "lean-4.19.0-linux/bin")).resolve()
    mathlib = Path(env.get("CROSSFOUR_MATHLIB", fallback / "mathlib4")).resolve()
    env.update(CROSSFOUR_LEAN_BIN=str(lean), CROSSFOUR_MATHLIB=str(mathlib),
               PATH=str(lean) + os.pathsep + env["PATH"])
    version = subprocess.check_output([lean / "lean", "--version"], text=True).strip()
    assert "version 4.19.0," in version and "commit 6caaee842e94," in version
    commit = subprocess.check_output(["git", "-C", mathlib, "rev-parse", "HEAD"], text=True).strip()
    assert commit == MATHLIB
    print(version, flush=True)
    print("Mathlib", commit, flush=True)
    assert check_manifest(HERE / "NEW-SOURCES.sha256", HERE) == [m + ".lean" for m in SOURCES]
    archive = HERE / PREVIOUS
    assert digest(archive) == ARCHIVE_SHA
    with ZipFile(archive) as frozen:
        assert frozen.testzip() is None
        frozen.extractall(stage)
    previous = stage / "graff384b-pendant-ranks"
    check_manifest(previous / "DELIVERY.sha256", previous)
    if args.checked:
        assert args.checked.read_bytes() == (previous / "StrictRanks.log").read_bytes()
        log = args.checked.read_text()
    else:
        log_path = stage / "predecessor.log"
        with log_path.open("w") as output:
            subprocess.run([sys.executable, "-B", previous / "replay.py", "--cold"], env=env, stdout=output,
                           stderr=subprocess.STDOUT, check=True)
        log = log_path.read_text()
    assert "Verified 6 fresh modules and 14 standard-axiom reports." in log
    assert "Verified the rank discount, second-edge incidence, and 27-high low-mate bounds, including weighted exposure and the third-ear quota." in log
    work = Path(re.search(r"^Pendant-rank replay (.+)$", log, re.M)[1])
    earlier = work / "baseline-objects"
    ears = work / "new/build"
    objects = stage / "baseline-objects"
    objects.mkdir()
    lines = (HERE / "PRIOR-OBJECTS.sha256").read_text().splitlines()
    assert len(lines) == len(set(line.split()[1] for line in lines)) == 187
    for line in lines:
        expected, name = line.split()
        matches = [path / name for path in (earlier, ears) if (path / name).is_file()]
        assert len(matches) == 1, name
        if args.checked:
            assert digest(matches[0]) == expected, name
        shutil.copy2(matches[0], objects / name)
    mode = "matched 187 compiled-object hashes" if args.checked else "rebuilt 187 predecessor modules"
    print("Verified pendant-rank source archive and delivery manifest;", mode, flush=True)
    libpath = subprocess.check_output([lean / "lake", "env", "printenv", "LEAN_PATH"],
                                      text=True, cwd=mathlib, env=env).strip()
    new = stage / "new"
    new.mkdir()
    (new / "build").mkdir()
    env["LEAN_PATH"] = os.pathsep.join(map(str, [new / "build", objects] +
                                           [(mathlib / part).resolve() for part in libpath.split(os.pathsep)]))
    for name in SOURCES:
        source = new / (name + ".lean")
        shutil.copy2(HERE / source.name, source)
        content = source.read_text()
        assert not re.search(r"\b(?:sorry|admit|native_decide|axiom)\b", content), name
        expected = re.findall(r"^#print axioms ([\w.]+)$", content, re.M)
        expected = [word if "." in word else "Graffiti384b." + word for word in expected]
        assert len(set(expected)) == len(expected) == SOURCES[name]
        target = new / "build" / (name + ".olean")
        command = [lean / "lean", "-j1", "-s", "65536", "-DElab.async=false",
                   "-DwarningAsError=true", "-o", target, source.name]
        proc = subprocess.run(command, cwd=new, env=env, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, text=True)
        (new / (name + ".log")).write_text(proc.stdout)
        print(proc.stdout, end="", flush=True)
        proc.check_returncode()
        assert target.stat().st_size > 0
        assert not re.search(r"\b(?:error|warning):|sorryAx", proc.stdout)
        reports = re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", proc.stdout, re.M)
        assert [theorem for theorem, _ in reports] == expected
        assert all(set(deps.split(", ")) <= AXIOMS for _, deps in reports)
    print(f"Verified {len(SOURCES)} fresh modules and {sum(SOURCES.values())} standard-axiom reports.")
    print("Verified the 26-vertex pool theorem, the full 27-high pendant and low-mate branch, and the residual independent-ear anchor bounds.")


if __name__ == "__main__":
    main()
