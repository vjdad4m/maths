"""Verify the physical row, released graph6 data and GraphCalc sample calls."""
import sys
import json
from collections import Counter
import subprocess
from importlib.metadata import version
from pathlib import Path

import graphcalc.graphs as gc
import networkx as nx

PIN = "4d1a8afc99447cacd2328cca20e47b6493e8dbc5"
ROW_ID = "99304c0e"
CLAIM = "(((nontrivial) ∧ (regular)) ∧ (triangle_free)) ⇒ average_degree ≤ min_maximal_matching_number"


def audit(checkout):
    head = subprocess.check_output(["git", "-C", checkout, "rev-parse", "HEAD"], text=True).strip()
    assert head == PIN
    results = checkout / "results"
    lines = (results / "survivors_by_touch_normalised.txt").read_text().splitlines()
    assert lines[1077] == f"[    68] {CLAIM}    -- promising:class"
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
    counts = Counter()
    for code in sorted(codes | backup):
        g = nx.from_graph6_bytes(code.encode())
        if not (gc.nontrivial(g) and gc.regular(g) and gc.triangle_free(g)):
            continue
        counts["eligible"] += 1
        counts["refutation_eligible"] += code in codes
        d = next(iter(g.degree))[1]
        assert gc.average_degree(g) == d
        # Each chosen edge covers at most 2d-1 edges including itself.
        if d == 0 or g.number_of_edges() > (d-1)*(2*d-1):
            counts["edge_count"] += 1
            continue
        # With d-1 chosen edges an uncovered vertex must remain. For
        # every possible such vertex, certify that an edge hits at most
        # one of its d neighbors. Covering its star then takes d edges.
        assert len(g) > 2*(d-1)
        for v in g:
            assert len(g[v]) == d
            assert all(int(a in g[v])+int(b in g[v]) <= 1 for a,b in g.edges)
        counts["neighborhood"] += 1
    assert (len(codes),len(backup),len(codes | backup)) == (312,4700,4776)
    assert counts == {"eligible":313, "refutation_eligible":72, "edge_count":255, "neighborhood":58}
    print("Row 1078, ID 99304c0e, proposed, 68 touches, null proof.")
    print("4776 distinct encodings, 313 eligible, 72 eligible in the three refutation files.")
    print("255 edge-count or degree-zero certificates and 58 local-neighborhood certificates.")


def samples():
    graphs = [
        ("empty graph on two vertices", nx.empty_graph(2), 0, 0),
        ("K2", nx.path_graph(2), 1, 1),
        ("C5", nx.cycle_graph(5), 2, 2),
        ("Petersen", nx.petersen_graph(), 3, 3),
        ("C8", nx.cycle_graph(8), 2, 3),
        ("K4,4", nx.complete_bipartite_graph(4,4), 4, 4),
        ("irregular P3", nx.path_graph(3), 4/3, 1),
        ("triangle K3", nx.complete_graph(3), 2, 1),
    ]
    for i,(name,g,average,optimal) in enumerate(graphs):
        assert gc.nontrivial(g)
        assert gc.regular(g) == (name != "irregular P3")
        assert gc.triangle_free(g) == (name != "triangle K3")
        assert gc.average_degree(g) == average and gc.min_maximal_matching_number(g) == optimal
        assert (average <= optimal) == (i < 6)
        print(f"{name}: average {average:g}, GraphCalc optimum {optimal}")


if __name__ == "__main__":
    assert version("graphcalc") == "2.0.0" and version("networkx") == "3.5"
    audit(Path(sys.argv[1]).resolve())
    samples()
