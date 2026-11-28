"""Replay the complete missing-one case and the ear-core reduction for Graffiti.pc 384b."""
from pathlib import Path
from io import BytesIO
import argparse
import hashlib
import os
import re
import subprocess
import tempfile
import zipfile

HERE = Path(__file__).resolve().parent
BASE = "graffiti-384b-single-leaf-cutoff-sources.zip"
BASE_SHA = "abe06d005062cddf33e5efe42dc7d678672adddf6fa9ec1d9e1e517ad140b28e"
MODULES = ["SplitShore", "CubicSide", "MatchingSide", "ShoreDonors", "EightExchange", "MissingOne", "EarComponent", "EarCoreReduction"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def sums(data):
    return {name: digest for digest, name in (line.split() for line in data.splitlines())}

def audit_predecessor(log, archive):
    for message in [
        "Verified 14 fresh modules and 30 standard-axiom reports.",
        "Verified 10 supplementary objects and 15 standard-axiom reports.",
        "Verified 5 leaf-stage modules and 18 standard-axiom reports.",
        "Verified 16 wheel-stage objects and 48 standard-axiom reports.",
        "Verified 3 original-edge objects and 8 standard-axiom reports.",
        "Verified 8 component-stage objects and 21 standard-axiom reports."
    ]:
        assert message in log, message
    paths = {name: Path(re.search("^" + name + " replay (.+)$", log, re.M)[1]) / "build"
             for name in ["Component", "Original-pin", "Wheel", "Leaf", "Linkage", "Odd-stars"]}
    with zipfile.ZipFile(archive) as comp:
        recent = sums(comp.read("OBJECTS.sha256").decode())
        with zipfile.ZipFile(BytesIO(comp.read("graffiti-384b-original-pins-sources.zip"))) as pins:
            orig = sums(pins.read("OBJECTS.sha256").decode())
            with zipfile.ZipFile(BytesIO(pins.read("graffiti-384b-wheel-cuts-sources.zip"))) as wh:
                upper = sums(wh.read("OBJECTS.sha256").decode())
                with zipfile.ZipFile(BytesIO(wh.read("graffiti-384b-leaf-cuts-sources.zip"))) as lf:
                    leaf = sums(lf.read("OBJECTS.sha256").decode())
                    with zipfile.ZipFile(BytesIO(lf.read("graffiti-384b-zero-nonleaf-sources.zip"))) as z:
                        linkage = sums(z.read("OBJECTS.sha256").decode())
                        with zipfile.ZipFile(BytesIO(z.read("graffiti-384b-odd-stars-sources.zip"))) as stars:
                            odd = sums(stars.read("NEW-OBJECTS.sha256").decode())
                            old = {n+".olean": digest for n,digest,_ in
                                   (line.split("\t") for line in stars.read("CHECKED-OBJECTS.tsv").decode().splitlines())}
    for name, manifest, count in [
        ("Odd-stars", old, 24), ("Odd-stars", odd, 14), ("Linkage", linkage, 10),
        ("Leaf", leaf, 5), ("Wheel", upper, 16), ("Original-pin", orig, 3), ("Component", recent, 8)
    ]:
        assert len(manifest) == count
        for n, digest in manifest.items():
            assert sha(paths[name] / n) == digest, (name,n)
    print("Authenticated all 80 predecessor objects.", flush=True)
    return list(paths.values())

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--component-log", type=Path, help="reuse a complete cold 80-module run after checking all expected objects")
    args = parser.parse_args()
    work = Path(tempfile.mkdtemp(dir=HERE, prefix=".missing-one."))
    print("Missing-one replay", work, flush=True)
    ml = Path(os.environ["CROSSFOUR_MATHLIB"]).resolve()
    lean = Path(os.environ["CROSSFOUR_LEAN_BIN"]).resolve()
    env = dict(os.environ, CROSSFOUR_MATHLIB=str(ml), CROSSFOUR_LEAN_BIN=str(lean))
    env["PATH"] = str(lean) + os.pathsep + env["PATH"]
    ver = subprocess.check_output([lean / "lean", "--version"], text=True).strip()
    assert "version 4.19.0," in ver and "commit 6caaee842e94," in ver
    assert subprocess.check_output(["git","-C",ml,"rev-parse","HEAD"], text=True).strip() == "c44e0c8ee63ca166450922a373c7409c5d26b00b"
    print(ver, flush=True)
    for name,digest in sums((HERE / "INPUTS.sha256").read_text()).items():
        assert sha(HERE / name) == digest, name
    archive = HERE / BASE
    assert sha(archive) == BASE_SHA
    if args.component_log:
        log = args.component_log.resolve().read_text()
    else:
        base = work / "components"
        with zipfile.ZipFile(archive) as z:
            z.extractall(base)
        r = subprocess.run(["python3","-B",base / "replay_components.py"], cwd=base, env=env,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        log = r.stdout
        (work / "ComponentsCold.log").write_text(log)
        print(log, flush=True)
        r.check_returncode()
    paths = audit_predecessor(log,archive)
    obj = work / "build"
    obj.mkdir()
    deps = subprocess.check_output([lean / "lake","env","printenv","LEAN_PATH"],
                                  cwd=ml,env=env,text=True).strip().split(os.pathsep)
    env["LEAN_PATH"] = os.pathsep.join(str(path) for path in [obj,*paths,*((ml / p).resolve() for p in deps)])
    sources = sums((HERE / "SOURCES.sha256").read_text())
    objects = sums((HERE / "OBJECTS.sha256").read_text())
    assert len(sources) == len(objects) == len(MODULES)
    report_count = 0
    for n in MODULES:
        f, o = n+".lean", n+".olean"
        assert sha(HERE/f) == sources[f]
        data = (HERE/f).read_text()
        assert not re.search(r"\b(?:sorry|admit|axiom|native_decide)\b", data)
        (work/f).write_bytes((HERE/f).read_bytes())
        r = subprocess.run([lean/"lean","-j1","-s","65536","-DElab.async=false","-DwarningAsError=true",
                            "-o",obj/o,f],cwd=work,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        print(r.stdout, end="", flush=True)
        (work/(n+".log")).write_text(r.stdout)
        r.check_returncode()
        assert not re.search(r"\b(?:warning|error):|sorryAx", r.stdout)
        labels = re.findall(r"^#print axioms ([\w.]+)$", data, re.M)
        reported = re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", r.stdout, re.M)
        assert labels and labels == [name for name,_ in reported]
        for _, axioms in reported:
            assert set(re.split(r",\s*", axioms.strip())) <= ALLOWED
        report_count += len(reported)
        assert sha(obj/o) == objects[o], n
    print(f"Verified {len(MODULES)} missing-one objects and {report_count} standard-axiom reports.", flush=True)

if __name__ == "__main__":
    main()
