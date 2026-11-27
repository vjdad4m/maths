"""Check the labeled counterexample through the upstream graphcalc.graphs entry points."""
from fractions import Fraction
from importlib.metadata import version

import graphcalc.graphs as gc
import networkx as nx

assert version("graphcalc") == "2.0.0"
graph = nx.path_graph(10)
for clone in range(10, 17):
    graph.add_edges_from(((0, clone), (2, clone)))

assert nx.is_connected(graph) and gc.nontrivial(graph) and gc.triangle_free(graph)
assert sorted(dict(graph.degree()).values(), reverse=True) == [9, 8] + [2]*14 + [1]
s = gc.sub_total_domination_number(graph)
b = gc.burning_number(graph, solver="cbc")
assert (graph.number_of_nodes(), s, b) == (17, 2, 4)
dist = dict(nx.all_pairs_shortest_path_length(graph))
sources = [0, 4, 7, 9]
assert all(any(dist[c][v] <= 3-i for i, c in enumerate(sources)) for v in graph)
assert b > Fraction(3, 2)*s
print(f"GraphCalc {version('graphcalc')}, NetworkX {version('networkx')}, PuLP {version('pulp')}")
print(f"order={len(graph)}, connected=True, triangle_free=True, sub_total={s}, burning={b}")
print(f"Row 362: {b} > {Fraction(3, 2)*s}. Four sources: {sources}")
