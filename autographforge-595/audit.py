"""Verify the physical row, released graph6 data and GraphCalc sample calls."""
import sys
import json
from fractions import Fraction
from math import isclose
import subprocess
from importlib.metadata import version
from pathlib import Path

import graphcalc.graphs as gc
import networkx as nx

PIN = "4d1a8afc99447cacd2328cca20e47b6493e8dbc5"
ROW_ID = "bc7d9697"
CLAIM = "(((nontrivial) ∧ (eulerian)) ∧ (regular)) ⇒ (harmonic_index + (-1/2)) ≤ matching_number"


def audit(checkout):
    head = subprocess.check_output(["git", "-C", checkout, "rev-parse", "HEAD"], text=True).strip()
    assert head == PIN
    results = checkout / "results"
    lines = (results / "survivors_by_touch_normalised.txt").read_text().splitlines()
    assert lines[594] == f"[   154] {CLAIM}    -- promising:class"
    assert sum(CLAIM in line for line in lines) == 1
    records = json.loads((results / "cegis_results.json").read_text())["conjectures"]
    record, = [r for r in records if r["id"] == ROW_ID]
    assert record["status"] == "proposed" and record["lean_proof"] is None and record["statement"] == CLAIM
    for proof in (results / "verified_proofs").glob("*.lean"):
        assert ROW_ID not in proof.read_text() and CLAIM not in proof.read_text()
    files = sorted(results.glob("*refuted.json"))
    assert len(files) == 3
    codes = set()
    for path in files:
        for r in json.loads(path.read_text()):
            assert r.get("id") != ROW_ID and r.get("statement") != CLAIM
            if r.get("witness_g6"):
                codes.add(r["witness_g6"])
    assert all(not w for r in records for w in r.get("tightness_witnesses", []))
    backups = subprocess.check_output(
        ["git", "-C", checkout, "ls-tree", "-r", "HEAD", "--", "results"], text=True
    ).splitlines()
    backups = [line for line in backups if line.endswith("/graphs.g6")]
    assert len(backups) == 4
    blobs = {line.split()[2] for line in backups}
    assert blobs == {"088f28b308df1405d6b63cfd44ec3931c1a9556e"}
    blob, = blobs
    backup = set(subprocess.check_output(
        ["git", "-C", checkout, "cat-file", "blob", blob], text=True
    ).splitlines())

    assert len(codes) == 312 and len(backup) == 4700 and len(codes | backup) == 4776

    eligible = refuted_eligible = 0
    failures = []
    for code in sorted(codes | backup):
        g = nx.from_graph6_bytes(code.encode())
        if not (gc.nontrivial(g) and gc.eulerian(g) and gc.regular(g)):
            continue
        eligible += 1
        refuted_eligible += code in codes
        h = sum(Fraction(2, g.degree(x)+g.degree(y)) for x,y in g.edges)
        assert h == Fraction(len(g), 2)
        assert isclose(gc.harmonic_index(g), float(h), rel_tol=1e-12)
        if gc.matching_number(g) < h - Fraction(1,2):
            failures.append(code)
    assert (eligible, refuted_eligible, failures) == (383, 62, [])
    print("Physical row 595; ID bc7d9697; 154 normalized touches; status proposed; null Lean proof.")
    print(f"{len(codes|backup)} released encodings; {eligible} eligible, including {refuted_eligible} from refutation JSON.")
    print("Released eligible counterexamples:", failures)

def example(s):
    g = nx.Graph()
    for i in range(s):
        for copy in (False, True):
            v = [(i,copy,j) for j in range(5)]
            g.add_edges_from((v[a],v[b]) for a in range(5) for b in range(a+1,5) if (a,b)!=(0,1))
            g.add_edges_from([(i,v[0]), ((i+1)%s,v[1])])
    return nx.convert_node_labels_to_integers(g)

if __name__ == "__main__":
    assert version("graphcalc") == "2.0.0" and version("networkx") == "3.5"
    audit(Path(sys.argv[1]).resolve())
    for s in [1,2,3,5]:
        g = example(s)
        assert gc.nontrivial(g) and gc.eulerian(g) and gc.regular(g)
        assert gc.harmonic_index(g) == 11*s/2 and gc.matching_number(g) == 5*s
        if s == 2:
            print("22-vertex graph6:", nx.to_graph6_bytes(g, header=False).decode().strip())
        print(f"{s} hubs; order {len(g)}; H={gc.harmonic_index(g)}; matching={gc.matching_number(g)}")
