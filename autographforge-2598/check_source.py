"""Audit the pinned AutoGraphForge row, released witnesses, and GraphCalc values."""
import json
import math
import subprocess
import sys
from collections import Counter
from fractions import Fraction
from importlib.metadata import version
from pathlib import Path

import graphcalc.graphs as gc
import networkx as nx

pin = "4d1a8afc99447cacd2328cca20e47b6493e8dbc5"
checkout = Path(sys.argv[1]).resolve()
assert subprocess.check_output(["git", "-C", checkout, "rev-parse", "HEAD"], text=True).strip() == pin
results = checkout / "results"
statement = "((nontrivial) ∧ (subcubic)) ⇒ average_shortest_path_length ≤ (((2/3) · harmonic_index) + (1/2))"
identifier = "a0a6bf25"
line = (results / "survivors_by_touch_normalised.txt").read_text().splitlines()[2597]
assert line == f"[     3] {statement}    -- promising:class"
record, = (r for r in json.loads((results / "cegis_results.json").read_text())["conjectures"]
           if r["id"] == identifier)
assert record["statement"] == statement and record["status"] == "proposed" and record["lean_proof"] is None
for proof in (results / "verified_proofs").glob("*.lean"):
    assert identifier not in proof.read_text() and statement not in proof.read_text()
print(f"Physical row 2598, ID {identifier}, status proposed, proof null.")


def invariants(graph):
    """Use ordered shortest-path sums and exact unordered edge weights."""
    ordered = sum(sum(row.values()) for _, row in nx.all_pairs_shortest_path_length(graph))
    n = len(graph)
    mean = Fraction(ordered, n * (n - 1))
    harmonic = sum(Fraction(2, graph.degree(u) + graph.degree(v)) for u, v in graph.edges)
    return mean, harmonic


def excess(mean, harmonic):
    return mean - Fraction(2, 3) * harmonic - Fraction(1, 2)


assert version("graphcalc") == "2.0.0" and version("networkx") == "3.5"
graph = nx.path_graph(9)
graph.add_edges_from([(1, 9), (7, 10)])
assert nx.is_tree(graph) and gc.nontrivial(graph) and gc.subcubic(graph)
mean, harmonic = invariants(graph)
assert (mean, harmonic, excess(mean, harmonic)) == (Fraction(204, 55), Fraction(24, 5), Fraction(1, 110))
assert gc.average_shortest_path_length(graph) == float(mean)
assert math.isclose(gc.harmonic_index(graph), float(harmonic), rel_tol=1e-15)
types = Counter(tuple(sorted((graph.degree(u), graph.degree(v)))) for u, v in graph.edges)
assert types == {(1, 3): 4, (2, 2): 4, (2, 3): 2}
print(f"GraphCalc {version('graphcalc')}, NetworkX {version('networkx')}, subcubic tree of order 11.")
print(f"Harmonic index {harmonic}, mean distance {mean}, bound 37/10, excess {excess(mean, harmonic)}.")

witnesses = set()
for name in ("cegis_refuted", "conjecturing_refuted", "property_conjecturing_refuted"):
    for record in json.loads((results / (name + ".json")).read_text()):
        assert record.get("id") != identifier and record.get("statement") != statement
        if record.get("witness_g6"):
            witnesses.add(record["witness_g6"])

eligible = disconnected = 0
for encoding in sorted(witnesses):
    g = nx.from_graph6_bytes(encoding.encode())
    if not gc.nontrivial(g) or not gc.subcubic(g):
        continue
    if not nx.is_connected(g):
        disconnected += 1
        try:
            gc.average_shortest_path_length(g)
        except nx.NetworkXError:
            continue
        raise AssertionError("Expected undefined mean on disconnected graph")
    eligible += 1
    assert excess(*invariants(g)) <= 0, encoding
assert (len(witnesses), eligible, disconnected) == (312, 64, 61)
print(f"Release audit: {len(witnesses)} distinct graph6 witnesses, {eligible} numerically eligible, "
      f"all satisfy the row; {disconnected} additional class members have undefined mean.")

count = 0
for order in range(2, 11):
    for tree in nx.nonisomorphic_trees(order):
        if gc.subcubic(tree):
            count += 1
            assert excess(*invariants(tree)) <= 0
print(f"Tree-only size check: all {count} subcubic tree isomorphism classes of orders 2 through 10 satisfy the row.")
