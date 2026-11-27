"""Confirm the release, screen every released witness, and solve the 14-vertex example."""
import json
import subprocess
import sys
from importlib.metadata import version
from itertools import combinations
from pathlib import Path

import graphcalc.graphs as gc
import networkx as nx

checkout = Path(sys.argv[1]).resolve()
pin = "4d1a8afc99447cacd2328cca20e47b6493e8dbc5"
assert subprocess.check_output(["git", "-C", checkout, "rev-parse", "HEAD"], text=True).strip() == pin
results = checkout / "results"
statement = "((nontrivial) ∧ (claw_free)) ⇒ vertex_clique_cover_number ≤ three_rainbow_domination_number"
identifier = "ae818342"
lines = (results / "survivors_by_touch_normalised.txt").read_text().splitlines()
assert lines[1706] == f"[    30] {statement}    -- promising:class"
assert sum(statement in line for line in lines) == 1
record, = (r for r in json.loads((results / "cegis_results.json").read_text())["conjectures"]
           if r["id"] == identifier)
assert record["statement"] == statement and record["status"] == "proposed" and record["lean_proof"] is None
for proof in (results / "verified_proofs").glob("*.lean"):
    assert identifier not in proof.read_text() and statement not in proof.read_text()
witnesses = set()
for name in ("cegis_refuted", "conjecturing_refuted", "property_conjecturing_refuted"):
    for record in json.loads((results / (name + ".json")).read_text()):
        assert record.get("id") != identifier and record.get("statement") != statement
        if record.get("witness_g6"):
            witnesses.add(record["witness_g6"])

def independent_set(g):
    free = set(g)
    chosen = []
    while free:
        v = min(free, key=lambda u: (len(free.intersection(g[u])), u))
        chosen.append(v)
        free.difference_update(g[v])
        free.remove(v)
    assert all(not g.has_edge(a, b) for a, b in combinations(chosen, 2))
    return chosen

eligible = 0
for encoding in sorted(witnesses):
    g = nx.from_graph6_bytes(encoding.encode())
    if not (gc.nontrivial(g) and gc.claw_free(g)):
        continue
    eligible += 1
    for component in nx.connected_components(g):
        h = g.subgraph(component)
        coloring = nx.greedy_color(nx.complement(h), strategy="saturation_largest_first")
        assert all(h.has_edge(a, b) or coloring[a] != coloring[b] for a, b in combinations(h, 2))
        upper = len(set(coloring.values()))
        n = len(h)
        degree = max(dict(h.degree).values())
        # 3(n-b) <= degree*b for any feasible set of b colored vertices.
        incidence = (3*n + degree + 2) // (degree + 3)
        # Row 720, applied only to nonsingleton connected claw-free components.
        independent = len(independent_set(h)) + (n > 1)
        lower = max(min(n, 3), sum(d < 3 for _, d in h.degree), incidence, independent)
        assert upper <= lower, encoding
print(f"Row 1707, {identifier}, proposed at pinned release, null proof, 30 normalized touches.")
print(f"All {eligible} eligible graphs among {len(witnesses)} distinct release witnesses satisfy the row.")

assert version("graphcalc") == "2.0.0" and version("networkx") == "3.5"
core = nx.mycielskian(nx.mycielskian(nx.complete_graph(2)))
assert len(core) == 11 and not any(nx.triangles(core).values())
padded = nx.disjoint_union(core, nx.empty_graph(3))
g = nx.complement(padded)
assert len(g) == 14 and gc.claw_free(g) and gc.nontrivial(g) and nx.is_connected(g)
cover, rainbow = gc.vertex_clique_cover_number(g), gc.three_rainbow_domination_number(g)
assert (cover, rainbow) == (4, 3)
print(f"GraphCalc 2.0.0, NetworkX 3.5: order={len(g)}, connected, claw-free, "
      f"clique partition={cover}, singleton three-rainbow={rainbow}.")
