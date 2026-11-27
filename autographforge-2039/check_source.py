"""Validate the exact row, both source diameter conventions and the released witnesses."""
import json
import math
import runpy
import subprocess
import sys
from fractions import Fraction
from importlib.metadata import version
from itertools import accumulate, combinations
from pathlib import Path

import graphcalc.graphs as gc
import networkx as nx

assert version("graphcalc") == "2.0.0" and version("networkx") == "3.5"
upstream = Path(sys.argv[1]).resolve()
pin = "4d1a8afc99447cacd2328cca20e47b6493e8dbc5"
assert subprocess.check_output(["git", "-C", upstream, "rev-parse", "HEAD"], text=True).strip() == pin
results = upstream / "results"
statement = "(((nontrivial) ∧ (K_4_free)) ∧ (claw_free)) ⇒ diameter ≤ (((43/15) · slater) + (4/15))"
assert (results / "survivors_by_touch_normalised.txt").read_text().splitlines()[2038] == (
    f"[    13] {statement}    -- promising:class")
record, = (c for c in json.loads((results / "cegis_results.json").read_text())["conjectures"]
           if c["id"] == "c6657d7f")
assert record["statement"] == statement and record["status"] == "proposed" and record["lean_proof"] is None
print("Physical row 2039, ID c6657d7f, status proposed, proof null.")

g = nx.path_graph(10)
g.add_edges_from((v, v+2) for v in range(4))
assert nx.is_connected(g) and gc.nontrivial(g) and gc.claw_free(g) and gc.K_4_free(g)
assert sorted((d for _, d in g.degree()), reverse=True) == [4,4,3,3,3,2,2,2,2,1]
wrapper = runpy.run_path(str(upstream / "graphs/invariants.py"))["diameter"]
s, d = gc.slater(g), gc.diameter(g)
rhs = Fraction(43*s + 4, 15)
assert (s, d, rhs) == (2, 7, 6) and wrapper(g) == d
print(f"GraphCalc {version('graphcalc')}, NetworkX {version('networkx')}, order={len(g)}, "
      f"K4-free=True, claw_free=True, Slater={s}, diameter={d}, wrapper={wrapper(g)}, RHS={rhs}")

old = nx.path_graph(7)
old.add_edge(7, 1)
for v in (8,9,10):
    old.add_edges_from(((1,v),(3,v)))
assert not gc.claw_free(old)
print("The earlier 11-vertex row-2223 witness fails the claw-free hypothesis.")

witnesses = set()
for name in ("cegis_refuted", "conjecturing_refuted", "property_conjecturing_refuted"):
    for entry in json.loads((results / (name+".json")).read_text()):
        assert entry.get("id") != record["id"] and entry.get("statement") != statement
        if entry.get("witness_g6"):
            witnesses.add(entry["witness_g6"])

connected = disconnected = 0
for encoded in sorted(witnesses):
    g = nx.from_graph6_bytes(encoded.encode())
    if len(g) < 2 or any(len(c) >= 4 for c in nx.find_cliques(g)):
        continue
    if any(all(not g.has_edge(a,b) for a,b in combinations(triple,2))
           for v in g for triple in combinations(g[v],3)):
        continue
    if not nx.is_connected(g):
        disconnected += 1
        assert wrapper(g) == math.inf
        try:
            gc.diameter(g)
        except nx.NetworkXError:
            continue
        raise AssertionError("Expected undefined finite diameter")
    connected += 1
    degrees = sorted((d for _,d in g.degree()), reverse=True)
    s = next(i for i, total in enumerate(accumulate(degrees), 1) if i + total >= len(g))
    assert 15*nx.diameter(g) <= 43*s + 4, encoded
print(f"Released corpus: {len(witnesses)} distinct graph6 witnesses, {connected} in finite domain, "
      f"none violates the finite bound. {disconnected} satisfy the classes and return +inf in the separate wrapper.")
