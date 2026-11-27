"""Run with GraphCalc 2.0.0, NetworkX 3.5, and a PuLP CBC solver."""
from fractions import Fraction
from importlib.metadata import version

import graphcalc.graphs as gc
import networkx as nx

assert version("graphcalc") == "2.0.0"
graph = nx.cycle_graph(12)
graph.add_edges_from((hub, v) for hub in (0, 12) for v in range(13, 23))
assert gc.nontrivial(graph) and gc.eulerian(graph) and gc.triangle_free(graph)
assert nx.is_connected(graph)
n = graph.number_of_nodes()
s = gc.slater(graph)
d = gc.diameter(graph)
b = gc.burning_number(graph, solver="cbc")
assert (n, s, d, b) == (23, 2, 8, 4)
print("order, Slater number, diameter, burning number", (n, s, d, b))
for row, lhs, rhs in ((747, b, Fraction(3, 2) * s),
                      (1889, b, Fraction(1, 3) * s + 3),
                      (2517, d, Fraction(14, 5) * s + Fraction(7, 5))):
    assert lhs > rhs
    print(f"Row {row}: {lhs} > {rhs}")
