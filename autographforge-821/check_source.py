"""Run with GraphCalc 2.0.0, NetworkX 3.5 and a checkout of pinned AutoGraphForge."""
import math
import runpy
import subprocess
import sys
from importlib.metadata import version
from pathlib import Path

import graphcalc.graphs as gc
import networkx as nx

assert version("graphcalc") == "2.0.0" and version("networkx") == "3.5"
repo = Path(sys.argv[1]).resolve()
pin = "4d1a8afc99447cacd2328cca20e47b6493e8dbc5"
assert subprocess.check_output(["git", "-C", repo, "rev-parse", "HEAD"], text=True).strip() == pin
row = (repo / "results/survivors_by_touch_normalised.txt").read_text().splitlines()[820]
print(row)
assert "(((nontrivial) ∧ (bipartite)) ∧ (chordal)) ⇒ diameter ≤ ((3 · slater) + -1)" in row
wrapper = runpy.run_path(str(repo / "graphs/invariants.py"))["diameter"]

isolates = nx.empty_graph(2)
assert gc.nontrivial(isolates) and gc.bipartite(isolates) and gc.chordal(isolates)
assert gc.slater(isolates) == 2
try:
    gc.diameter(isolates)
except nx.NetworkXError:
    pass
else:
    raise AssertionError("Expected disconnected GraphCalc diameter to be undefined")
assert wrapper(isolates) == math.inf
print("Two isolates: GraphCalc diameter undefined, wrapper +infinity, right side 5")

path = nx.path_graph(9)
assert gc.nontrivial(path) and gc.bipartite(path) and gc.chordal(path)
assert gc.diameter(path) == wrapper(path) == 8 == 3 * gc.slater(path) - 1
print("Nine-vertex path: finite diameter 8, Slater number 3, equality")
