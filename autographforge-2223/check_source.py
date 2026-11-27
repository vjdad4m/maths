"""Check the 11-vertex certificate and the earlier 17-vertex witness in GraphCalc."""
from importlib.metadata import version

import graphcalc.graphs as gc
import networkx as nx

assert version("graphcalc") == "2.0.0"
print(f"GraphCalc {version('graphcalc')}, NetworkX {version('networkx')}")
graph = nx.path_graph(7)
graph.add_edge(7, 1)
for clone in (8, 9, 10):
    graph.add_edges_from(((1, clone), (3, clone)))
assert gc.nontrivial(graph) and gc.K_4_free(graph) and nx.is_connected(graph)
assert nx.is_bipartite(graph)
degrees = sorted((d for _, d in graph.degree()), reverse=True)
assert degrees == [6, 5] + [2]*6 + [1]*3
distances = tuple(nx.shortest_path_length(graph, a, b) for a, b in ((0,7), (7,6), (6,0)))
assert distances == (2, 6, 6)
s, t = gc.sub_total_domination_number(graph), gc.triameter(graph)
assert (len(graph), s, t) == (11, 2, 14)
assert t > 4*s+4
print(f"order={len(graph)}, K4-free=True, connected=True, degrees={degrees}")
print(f"distances of triple (0,7,6)={distances}, triameter={t}, sub_total={s}, RHS={4*s+4}")

earlier = nx.path_graph(10)
for clone in range(10, 17):
    earlier.add_edges_from(((0, clone), (2, clone)))
assert gc.nontrivial(earlier) and gc.K_4_free(earlier) and nx.is_connected(earlier)
assert (gc.triameter(earlier), gc.sub_total_domination_number(earlier)) == (18, 2)
print("Earlier row-362 witness on 17 vertices: triameter=18, sub_total=2.")
