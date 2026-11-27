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
ROW_ID = "d7f95ad0"
CLAIM = "(((nontrivial) ∧ (K_4_free)) ∧ (eulerian)) ⇒ slater ≤ min_maximal_matching_number"


def audit(checkout):
    head = subprocess.check_output(["git", "-C", checkout, "rev-parse", "HEAD"], text=True).strip()
    assert head == PIN
    results = checkout / "results"
    lines = (results / "survivors_by_touch_normalised.txt").read_text().splitlines()
    assert lines[582] == f"[   160] {CLAIM}    -- promising:class"
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
    counts = Counter()
    for code in sorted(codes | backup):
        graph = nx.from_graph6_bytes(code.encode())
        if not (gc.nontrivial(graph) and gc.eulerian(graph) and gc.K_4_free(graph)):
            continue
        counts["eligible"] += 1
        counts["from_refutations"] += code in codes
        caps = sorted((d + 1 for _, d in graph.degree()), reverse=True)
        assert min(caps) >= 3
        t = gc.slater(graph)
        assert t > 0 and sum(caps[:t - 1]) < len(graph) <= sum(caps[:t])
        # Every set of t-1 edges has at most 2(t-1) endpoints. Their total
        # capacity is too small to meet every closed neighborhood twice.
        assert sum(caps[:2 * (t - 1)]) < 2 * len(graph)
    assert counts == {"eligible": 586, "from_refutations": 84}
    print("Row 583, ID d7f95ad0, 160 touches, proposed with null proof.")
    print(f"4776 distinct released encodings; {counts['eligible']} eligible, "
          f"including {counts['from_refutations']} from released refutations.")

def make_graph(k, compact=False):
    graph = nx.Graph()
    for i in range(k):
        graph.add_edge(2*i, 2*i+1)

    def connector(a, b):
        new_vertex = len(graph)
        graph.add_edges_from([(a, new_vertex), (b, new_vertex)])

    for i in range(k):
        connector(2*i, 2*((i+1) % k)+1)
    for a in range(2*k):
        for b in range(2*k):
            if a//2 == b//2 or (compact and a >= b):
                continue
            for _ in range(1 if compact else 2*k):
                connector(a, b)
    return graph


def direct(k, compact):
    graph = make_graph(k, compact)
    assert gc.nontrivial(graph) and gc.K_4_free(graph) and gc.eulerian(graph)
    values = (gc.slater(graph), gc.min_maximal_matching_number(graph), gc.domination_number(graph))
    assert values == (k, k, 2*k - 1)
    print(f"order {len(graph)}, size {graph.number_of_edges()}: "
          f"Slater, edge domination, vertex domination = {values}.")


if __name__ == "__main__":
    assert version("graphcalc") == "2.0.0" and version("networkx") == "3.5"
    audit(Path(sys.argv[1]).resolve())
    direct(2, True)
    direct(2, False)
    direct(3, False)
    path = nx.path_graph(4)
    assert (gc.slater(path), gc.min_maximal_matching_number(path)) == (2, 1)
    print("P4 has minimum degree one, Slater 2 and edge domination 1.")
