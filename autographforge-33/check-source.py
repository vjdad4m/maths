"""Check the pinned release and run GraphCalc's Slater and burning entry points."""
import argparse
import json
import subprocess
from pathlib import Path

import graphcalc.graphs as gc
import networkx as nx


RELEASE_COMMIT = "4d1a8afc99447cacd2328cca20e47b6493e8dbc5"
GRAPHCALC_COMMIT = "ce66ac7390d945885e33f372e29c896fa32e9bc4"
STATEMENT = "((nontrivial) ∧ (connected)) ⇒ burning_number ≤ (slater + 1)"
EQUIVALENT = "((nontrivial) ∧ (connected)) ⇒ (burning_number + -1) ≤ slater"
RECORDS = {"fe71fb58": STATEMENT, "de34b0ca": EQUIVALENT}


def head(checkout):
    return subprocess.check_output(
        ["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True
    ).strip()


def check_release(checkout):
    assert head(checkout) == RELEASE_COMMIT
    results = checkout / "results"
    lines = (results / "survivors_by_touch_normalised.txt").read_text().splitlines()
    raw = (results / "survivors_by_touch.txt").read_text().splitlines()
    assert lines[32] == raw[21]
    for line, statement in [(raw[21], STATEMENT), (raw[22], EQUIVALENT)]:
        assert line.split("] ", 1)[1].split("    --", 1)[0] == statement
        assert line.endswith("-- promising:class")
    records = json.loads((results / "cegis_results.json").read_text())["conjectures"]
    selected = {r["id"]: r for r in records if r["id"] in RECORDS}
    for ident, statement in RECORDS.items():
        assert selected[ident]["statement"] == statement
        assert selected[ident]["status"] == "proposed"
        assert selected[ident]["lean_proof"] is None
    refuted = json.loads((results / "cegis_refuted.json").read_text())
    assert not any(r["id"] in RECORDS or r["statement"] in RECORDS.values() for r in refuted)
    for proof in (results / "verified_proofs").rglob("*.lean"):
        contents = proof.name + proof.read_text()
        assert not any(ident in contents for ident in RECORDS)
    audits = json.loads((results / "audit_top_normalised.json").read_text())["conjectures"]
    audit, = (r for r in audits if r["statement"] == STATEMENT)
    assert audit["bucket"] == "promising:class" and not audit["decorative"]
    assert audit["known_as"] is None and audit["subsumed_by"] is None
    print(f"AutoGraphForge {RELEASE_COMMIT}, normalized 33, raw 22 and equivalent raw 23")
    print(STATEMENT, "IDs", ", ".join(RECORDS))
    print("Release status proposed. Generation touches", audit["touch_generation"])


def check_graphcalc():
    checkout = Path(gc.__file__).resolve().parents[3]
    assert head(checkout) == GRAPHCALC_COMMIT
    graph = nx.lollipop_graph(8, 8)
    assert set(graph) == set(range(16))
    assert all(graph.has_edge(x, y) == (y < 8 or x+1 == y)
               for x in range(16) for y in range(x+1, 16))
    assert gc.nontrivial(graph) and gc.connected(graph)
    slater = gc.slater(graph)
    burning, schedule = gc.burning_number(graph, return_schedule=True)
    assert (slater, burning) == (2, 4) and len(schedule) == 4
    assert all(any(nx.shortest_path_length(graph, center, v) <= 3-t
                   for t, center in enumerate(schedule)) for v in graph)
    print(f"GraphCalc {GRAPHCALC_COMMIT}, NetworkX {nx.__version__}, K8 with an 8-vertex tail")
    print(f"Slater = {slater}, burning = {burning}, violating 4 ≤ 3")
    print(f"Validated four-round GraphCalc schedule {schedule}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("release", type=Path, help="AutoGraphForge release checkout")
    check_release(parser.parse_args().release)
    check_graphcalc()
