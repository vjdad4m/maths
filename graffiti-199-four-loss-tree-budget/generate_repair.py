"""Emit the six exceptional rows' forced-tree and spanning-path certificates."""
from itertools import combinations
from pathlib import Path
import ast
import re
import sys

source = Path(sys.argv[1]).read_text()
rows = ast.literal_eval("[" + re.search(r"def halves .*?:=\n  \(\s*#\[(.*?)\] : Array", source)[1] + "]")
highs = (1, 2, 3, 5, 6, 7)
forbidden = {(1, 3), (2, 3), (5, 7), (6, 7), (3, 7)}
fixed = {(0, 1), (0, 2), (0, 3), (1, 2), (4, 5), (4, 6), (4, 7), (5, 6), (8, 9)}
all_vertices = set(range(10))

def edge(a, b):
    return tuple(sorted((a, b)))

def tree_order(vertices, edges):
    order = [vertices[0]]
    for a in order:
        for b in vertices:
            if edge(a, b) in edges and b not in order:
                order.append(b)
    return order if len(order) == len(vertices) else []

def find_path(edges, end):
    def visit(path, pending):
        if not pending:
            return path[::-1]
        for v in sorted(pending):
            if edge(path[-1], v) in edges:
                result = visit(path + [v], pending - {v})
                if result:
                    return result
        return []
    return visit([end], all_vertices - {end})

def repair(row):
    a, b, c, d = rows[row]
    edges = fixed | {edge(a, b), edge(c, d), (a, 8), (b, 8), (c, 9), (d, 9)}
    steps = []
    while not all(find_path(edges, tip) for tip in highs):
        optional = set(combinations(highs, 2)) - forbidden - edges
        forced = {}
        for vertices in combinations(sorted(all_vertices), 6):
            pairs = set(combinations(vertices, 2))
            if len(pairs & edges) != 5 or len(pairs & optional) != 1:
                continue
            if order := tree_order(vertices, edges):
                forced.setdefault(next(iter(pairs & optional)), order)
        assert forced
        for chord, order in sorted(forced.items()):
            steps.append((chord, order))
            edges.add(chord)
    return steps, [find_path(edges, v) if v in highs else [] for v in range(8)]

certificates = {r: repair(r) for r in range(18, 24)}
print("""import SplitTipsLocal
import DepletedPaths

namespace Graffiti199Depleted.TreeRepair

open Graffiti199K2.NearPacking.Depleted

structure ForcingStep where
  chord : K × K
  witness : Fin 6 → K

def repair (r : Row) : List ForcingStep :=
  match r.val with""")
for r, (steps, _) in certificates.items():
    code = ", ".join(f"⟨{chord}, !{order}⟩" for chord, order in steps)
    print(f"  | {r} => [{code}]")
print("""  | _ => []

def route (r : Row) (i : I) : List K :=
  (match r.val with""")
for r, (_, paths) in certificates.items():
    print(f"  | {r} => #{paths}")
print("""  | _ => #[] : Array (List K)).getD i.val []

end Graffiti199Depleted.TreeRepair""")
