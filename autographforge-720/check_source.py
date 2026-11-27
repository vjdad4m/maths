"""Check the physical row and status, released refutations, and GraphCalc controls."""
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
statement = "(((nontrivial) ∧ (claw_free)) ∧ (connected)) ⇒ (independence_number + 1) ≤ three_rainbow_domination_number"
identifier = "f6e3f6c0"
lines = (results / "survivors_by_touch_normalised.txt").read_text().splitlines()
assert lines[719] == f"[   112] {statement}    -- promising:class"
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

eligible = 0
for encoding in sorted(witnesses):
    g = nx.from_graph6_bytes(encoding.encode())
    if gc.nontrivial(g) and gc.claw_free(g) and nx.is_connected(g):
        eligible += 1
print(f"Physical row 720, ID {identifier}, proposed, proof null, 112 normalized touches.")
print(f"Release: {len(witnesses)} distinct graph6 witnesses; {eligible} meet the row hypotheses.")
assert version("graphcalc") == "2.0.0" and version("networkx") == "3.5"
edge_plus_isolates = nx.empty_graph(5)
edge_plus_isolates.add_edge(0, 1)
for label, graph, expected in [
    ("K2", nx.path_graph(2), (1, 2)),
    ("P3", nx.path_graph(3), (2, 3)),
    ("K4", nx.complete_graph(4), (1, 3)),
    ("K2 plus three isolates", edge_plus_isolates, (4, 5)),
    ("two isolates", nx.empty_graph(2), (2, 2)),
]:
    assert gc.nontrivial(graph) and gc.claw_free(graph)
    values = gc.independence_number(graph), gc.three_rainbow_domination_number(graph)
    assert values == expected, (label, values)
    print(f"{label}: alpha={values[0]}, singleton rainbow={values[1]}, connected={nx.is_connected(graph)}.")
