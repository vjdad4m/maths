"""Run with GraphCalc 2.0.0, NetworkX 3.5 and the PuLP CBC solver."""
from importlib.metadata import version

import graphcalc.graphs as gc
import networkx as nx

assert version("graphcalc") == "2.0.0"
assert version("networkx") == "3.5"

# The enumeration matches the edge labels used by the Lean proof.
edges = [(0, 2), (1, 2), (0, 3), (1, 3)]
edges += list(zip([0, *range(4, 13)], [*range(4, 13), 0]))
original = nx.Graph(edges)
labels = {frozenset(e): i for i, e in enumerate(edges)}
line = nx.line_graph(original)
graph = nx.relabel_nodes(line, {e: labels[frozenset(e)] for e in line})
assert set(graph) == set(range(14))
assert gc.nontrivial(graph) and gc.claw_free(graph) and gc.eulerian(graph)
assert sorted(dict(graph.degree()).values(), reverse=True) == [4] * 4 + [2] * 10
s = gc.slater(graph)
b = gc.burning_number(graph, solver="cbc")
assert (s, b) == (3, 4)
distance = dict(nx.all_pairs_shortest_path_length(graph))
cycle = range(4, 14)
for x in graph:
    for r in range(5):
        assert sum(distance[x][v] <= r for v in cycle) <= 2 * r + 1
for x in cycle:
    for y in cycle:
        assert distance[x][y] == min(abs(x-y), 10-abs(x-y))
schedule = (0, 5, 8, 10)
assert all(any(distance[x][v] <= 3-i for i, x in enumerate(schedule)) for v in graph)
assert 2*b - 4 > s
print(f"Order {len(graph)}, connected {nx.is_connected(graph)}, Eulerian and claw-free")
print(f"Slater {s}, burning {b}, row 895 violates {2*b-4} ≤ {s}")
