"""Verify release identity and GraphCalc's exact clique-partition and Roman optimizers."""
import json
import subprocess
import sys
from importlib.metadata import version
from pathlib import Path

import graphcalc.graphs as gc
import networkx as nx

checkout = Path(sys.argv[1]).resolve()
pin = "4d1a8afc99447cacd2328cca20e47b6493e8dbc5"
assert subprocess.check_output(["git", "-C", checkout, "rev-parse", "HEAD"], text=True).strip() == pin
results = checkout / "results"
statement = "(((nontrivial) ∧ (claw_free)) ∧ (subcubic)) ⇒ vertex_clique_cover_number ≤ roman_domination_number"
identifier = "0ec32efb"
lines = (results / "survivors_by_touch_normalised.txt").read_text().splitlines()
assert lines[620] == f"[   146] {statement}    -- promising:class"
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
eligible = small = 0
for encoding in sorted(witnesses):
    g = nx.from_graph6_bytes(encoding.encode())
    if not (gc.nontrivial(g) and gc.claw_free(g) and gc.subcubic(g)):
        continue
    eligible += 1
    if len(g) <= 12:
        assert gc.vertex_clique_cover_number(g) <= gc.roman_domination_number(g), encoding
        small += 1
print(f"Physical row 621, ID {identifier}, proposed, null proof, 146 normalized touches.")
print(f"{len(witnesses)} distinct released graph6 witnesses; {eligible} satisfy the hypotheses. "
      f"GraphCalc checked all {small} eligible witnesses of order at most 12.")
assert version("graphcalc") == "2.0.0" and version("networkx") == "3.5"
for label, graph, expected in [
    ("P3", nx.path_graph(3), (True, True, 2, 2)),
    ("K4", nx.complete_graph(4), (True, True, 1, 2)),
    ("two isolates", nx.empty_graph(2), (True, True, 2, 2)),
    ("four-rim wheel", nx.wheel_graph(5), (True, False, 2, 2)),
    ("five-rim wheel", nx.wheel_graph(6), (True, False, 3, 2)),
]:
    result = (gc.claw_free(graph), gc.subcubic(graph), gc.vertex_clique_cover_number(graph),
              gc.roman_domination_number(graph))
    assert result == expected, (label, result)
    print(f"{label}: claw-free={result[0]}, subcubic={result[1]}, maximum degree={max(dict(graph.degree).values())}, "
          f"clique partition={result[2]}, Roman={result[3]}.")
