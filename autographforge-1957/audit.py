"""Verify the physical row, released graph6 data and GraphCalc sample calls."""
import sys
import json
import subprocess
from importlib.metadata import version
from pathlib import Path

import graphcalc.graphs as gc
import networkx as nx

PIN = "4d1a8afc99447cacd2328cca20e47b6493e8dbc5"
ROW_ID = "b25512ac"
CLAIM = "(((nontrivial) ∧ (connected)) ∧ (regular)) ⇒ vertex_clique_cover_number ≤ (((4/3) · min_maximal_matching_number) + 1)"


def audit(checkout):
    head = subprocess.check_output(["git", "-C", checkout, "rev-parse", "HEAD"], text=True).strip()
    assert head == PIN
    results = checkout / "results"
    lines = (results / "survivors_by_touch_normalised.txt").read_text().splitlines()
    assert lines[1956] == f"[    17] {CLAIM}    -- promising:class"
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

    eligible = 0
    refuted_eligible = 0
    failures = []
    family_matches = []
    for code in sorted(codes | backup):
        g = nx.from_graph6_bytes(code.encode())
        if not (gc.nontrivial(g) and gc.connected(g) and gc.regular(g)):
            continue
        eligible += 1
        refuted_eligible += code in codes
        n = len(g)
        d = next(iter(dict(g.degree()).values()))
        if d >= 4 and n == 4*d-2 and nx.is_isomorphic(g, twin(d)):
            family_matches.append((code,n,d))
        if d != 2 or n == 3:
            continue
        # A connected simple 2-regular graph is a cycle. Each clique covers
        # at most two vertices and a cycle edge dominates at most three edges.
        # Consecutive pairs, respectively every third edge, attain the ceilings.
        theta = (n+1)//2
        edge = (n+2)//3
        if 3*theta > 4*edge+3:
            failures.append((code,n,theta,edge))
    assert (eligible,refuted_eligible) == (567,97)
    assert len(failures) == 28 and not family_matches
    print("Row 1957, b25512ac, proposed, null Lean proof; 17 normalized touches.")
    print(f"{len(codes|backup)} distinct codes; {eligible} eligible; {refuted_eligible} eligible from refutation JSON.")
    print("Released violating cycle orders:", sorted(n for _,n,_,_ in failures))
    print("Released encodings isomorphic to a violating twin family member:",family_matches)
    raw = subprocess.check_output(["git","-C",checkout,"cat-file","blob",blob],text=True).splitlines()
    for code,n,theta,edge in failures:
        if n in (21,24):
            assert nx.is_isomorphic(nx.from_graph6_bytes(code.encode()),nx.cycle_graph(n))
            assert gc.min_maximal_matching_number(nx.cycle_graph(n)) == edge
            print(f"C{n}: clique cover {theta}, line domination {edge}; backup line {raw.index(code)+1}, code {code}")

def twin(d):
    # Two K_{d,d-1} copies. Each core lies in exactly one joining edge.
    g = nx.Graph()
    for b in range(2):
        for i in range(d):
            core = (2*d-1)*b + i
            for j in range(d-1):
                g.add_edge(core,(2*d-1)*b+d+j)
    for i in range(d):
        g.add_edge(i,2*d-1+i)
    return g

if __name__ == "__main__":
    assert version("graphcalc") == "2.0.0" and version("networkx") == "3.5"
    audit(Path(sys.argv[1]).resolve())
    for d in (2,3,4,5):
        g=twin(d)
        assert gc.nontrivial(g) and gc.connected(g) and gc.regular(g) and gc.bipartite(g)
        assert len(g) == 4*d-2 and gc.min_maximal_matching_number(g) == d
        # A triangle-free graph with a perfect matching has clique cover n/2.
        match=nx.max_weight_matching(g,maxcardinality=True)
        assert len(match) == 2*d-1 and not any(nx.triangles(g).values())
        if d <= 3:
            assert gc.vertex_clique_cover_number(g) == 2*d-1
        print(f"Degree {d}: order {len(g)}, clique cover {2*d-1}, line domination {d}")
        if d==4:
            print("14-vertex graph6:",nx.to_graph6_bytes(g,header=False).decode().strip())
