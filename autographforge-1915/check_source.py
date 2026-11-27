"""Reproduce row 1915 on the pinned GraphCalc and NetworkX implementations."""
from importlib.metadata import version
from itertools import combinations
from pathlib import Path
import subprocess
import sys

import graphcalc.graphs as gc
import networkx as nx

assert version("graphcalc") == "2.0.0" and version("networkx") == "3.5"
repo = Path(sys.argv[1]).resolve()
pin = "4d1a8afc99447cacd2328cca20e47b6493e8dbc5"
assert subprocess.check_output(["git", "-C", repo, "rev-parse", "HEAD"], text=True).strip() == pin
row = (repo / "results/survivors_by_touch_normalised.txt").read_text().splitlines()[1914]
statement = "(((nontrivial) ∧ (chordal)) ∧ (eulerian)) ⇒ (2 · slater) ≤ maximum_degree"
assert row.split("] ", 1)[1].split("    --", 1)[0] == statement

def triangle_chain(t):
    graph = nx.Graph()
    for i in range(t):
        graph.add_edges_from(combinations([2*i, 2*i+1, 2*i+2], 2))
    return graph

for t in range(1, 25):
    graph = triangle_chain(t)
    assert gc.nontrivial(graph) and gc.eulerian(graph) and gc.chordal(graph)
    n = graph.number_of_nodes()
    s, delta = gc.slater(graph), gc.maximum_degree(graph)
    assert n == 2*t + 1
    assert sorted(d for _, d in graph.degree()) == [2]*(t+2) + [4]*(t-1)
    assert delta == (2 if t == 1 else 4)
    assert n <= s * (delta + 1)
    if t >= 5:
        assert 2*s > delta
    if t == 5:
        assert (n, s, delta) == (11, 3, 4)
        print(f"Row 1915: {n} vertices, Slater {s}, maximum degree {delta}; {2*s} > {delta}")
print("GraphCalc checked all three hypotheses and both invariants for chains of 1–24 triangles.")
