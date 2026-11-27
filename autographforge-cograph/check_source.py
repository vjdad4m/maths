"""Reproduce the GraphCalc domain checks; pass a checkout of pinned AutoGraphForge."""
from importlib.metadata import version
from itertools import combinations
from math import inf
from pathlib import Path
import runpy
import subprocess
import sys

import graphcalc.graphs as gc
import networkx as nx

assert version("graphcalc") == "2.0.0" and version("networkx") == "3.5"
repo = Path(sys.argv[1]).resolve()
pin = "4d1a8afc99447cacd2328cca20e47b6493e8dbc5"
assert subprocess.check_output(["git", "-C", repo, "rev-parse", "HEAD"], text=True).strip() == pin
rows = (repo / "results/survivors_by_touch_normalised.txt").read_text().splitlines()
statements = {
    143: "(((nontrivial) ∧ (cograph)) ∧ (connected)) ⇒ radius = slater",
    818: "(((nontrivial) ∧ (cograph)) ∧ (regular)) ⇒ diameter ≤ slater",
    1128: "(((nontrivial) ∧ (cograph)) ∧ (regular)) ⇒ triameter ≤ (3 · slater)",
}
for number, statement in statements.items():
    assert rows[number-1].split("] ", 1)[1].split("    --", 1)[0] == statement

graph_count = connected_cographs = regular_connected_cographs = 0
for g in nx.graph_atlas_g():
    graph_count += 1
    # An induced simple graph on four vertices with degrees 1,1,2,2 is P4.
    free = all(sorted(d for _, d in g.subgraph(s).degree()) != [1, 1, 2, 2]
               for s in combinations(g.nodes, 4))
    assert gc.cograph(g) == free
    if not (gc.nontrivial(g) and free and gc.connected(g)):
        continue
    connected_cographs += 1
    assert gc.radius(g) == gc.slater(g)
    if gc.regular(g):
        regular_connected_cographs += 1
        assert gc.diameter(g) <= gc.slater(g)
        assert gc.triameter(g) <= 3 * gc.slater(g)

print(f"Atlas: {graph_count} cograph tests, {connected_cographs} row 143 cases, "
      f"{regular_connected_cographs} cases for each of rows 818 and 1128")
assert gc.triameter(nx.path_graph(2)) == 0
w = nx.empty_graph(2)
assert gc.nontrivial(w) and gc.regular(w) and gc.cograph(w) and gc.slater(w) == 2
for f, error in ((gc.diameter, nx.NetworkXError), (gc.radius, nx.NetworkXError),
                 (gc.triameter, ValueError)):
    try:
        f(w)
    except error:
        pass
    else:
        raise AssertionError(f"Expected undefined {f.__name__} on two isolates")
wrapper = runpy.run_path(str(repo / "graphs/invariants.py"))
assert wrapper["INVARIANTS"]["diam"](w) == inf
assert wrapper["INVARIANTS"]["rad"](w) == inf
assert "triameter" not in wrapper and "triameter" not in wrapper["INVARIANTS"]
print("Two isolates: Slater 2, GraphCalc distance functions undefined, "
      "wrapper diameter and radius +infinity, no wrapper triameter")

