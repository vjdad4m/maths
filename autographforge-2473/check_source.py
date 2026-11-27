"""Check the exact row, GraphCalc result and all upstream refutation witnesses."""
import json
import subprocess
import sys
from collections import Counter
from fractions import Fraction
from importlib.metadata import version
from itertools import accumulate, combinations
from pathlib import Path

import graphcalc.graphs as gc
import networkx as nx

pin = "4d1a8afc99447cacd2328cca20e47b6493e8dbc5"
checkout = Path(sys.argv[1]).resolve()
assert subprocess.check_output(["git", "-C", checkout, "rev-parse", "HEAD"], text=True).strip() == pin
results = checkout / "results"
statement = "(((nontrivial) ∧ (K_4_free)) ∧ (claw_free)) ⇒ average_shortest_path_length ≤ ((7/5) · slater)"
identifier = "27d9e7c4"
assert (results/"survivors_by_touch_normalised.txt").read_text().splitlines()[2472] == (
    f"[     4] {statement}    -- promising:class")
record, = (r for r in json.loads((results/"cegis_results.json").read_text())["conjectures"]
           if r["id"] == identifier)
assert record["statement"] == statement and record["status"] == "proposed" and record["lean_proof"] is None
for proof in (results/"verified_proofs").glob("*.lean"):
    assert identifier not in proof.read_text() and statement not in proof.read_text()
print(f"Physical row 2473, ID {identifier}, status proposed, proof null.")

graph = nx.path_graph(10)
graph.add_edges_from((i, i+2) for i in range(4))
assert version("graphcalc") == "2.0.0" and version("networkx") == "3.5"
assert nx.is_connected(graph) and gc.nontrivial(graph) and gc.K_4_free(graph) and gc.claw_free(graph)
s = gc.slater(graph)
dist = dict(nx.all_pairs_shortest_path_length(graph))
counts = Counter(dist[u][v] for u, v in combinations(graph, 2))
assert [counts[i] for i in range(1, 8)] == [13, 10, 7, 6, 5, 3, 1]
total = sum(k*v for k,v in counts.items())
mean = Fraction(total, sum(counts.values()))
assert total == 128 and mean == Fraction(128,45) and s == 2
assert gc.average_shortest_path_length(graph) == float(mean)
margin = mean - Fraction(7*s,5)
assert margin == Fraction(2,45)
print(f"GraphCalc {version('graphcalc')}, NetworkX {version('networkx')}, order=10, "
      f"connected=True, K4-free=True, claw-free=True, Slater={s}.")
print(f"Unordered distance histogram={sorted(counts.items())}; exact mean={mean}, "
      f"bound={Fraction(7*s,5)}, excess={margin}.")

witnesses = set()
for name in ("cegis_refuted", "conjecturing_refuted", "property_conjecturing_refuted"):
    for record in json.loads((results/(name+".json")).read_text()):
        assert record.get("id") != identifier and record.get("statement") != statement
        if record.get("witness_g6"):
            witnesses.add(record["witness_g6"])
eligible = disconnected = 0
for encoding in sorted(witnesses):
    g = nx.from_graph6_bytes(encoding.encode())
    if len(g) < 2 or any(len(c) >= 4 for c in nx.find_cliques(g)):
        continue
    if any(all(not g.has_edge(a,b) for a,b in combinations(triple,2))
           for v in g for triple in combinations(g[v],3)):
        continue
    if not nx.is_connected(g):
        disconnected += 1
        try:
            gc.average_shortest_path_length(g)
        except nx.NetworkXError:
            continue
        raise AssertionError("Expected undefined average distance")
    eligible += 1
    degrees = sorted((d for _, d in g.degree()), reverse=True)
    s = next(i for i, z in enumerate(accumulate(degrees), 1) if i + z >= len(g))
    total = sum(sum(d.values()) for _,d in nx.all_pairs_shortest_path_length(g))
    assert 5*total <= 7*s*len(g)*(len(g)-1), encoding
print(f"{len(witnesses)} distinct released graph6 witnesses, {eligible} in the numerical domain, "
      f"none violates the inequality. {disconnected} other class members have undefined mean distance.")
