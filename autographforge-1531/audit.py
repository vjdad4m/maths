"""Verify the physical row, released graph6 data and GraphCalc sample calls."""
import sys
import json
import subprocess
from importlib.metadata import version
from pathlib import Path

import graphcalc.graphs as gc
import networkx as nx

PIN = "4d1a8afc99447cacd2328cca20e47b6493e8dbc5"
ROW_ID = "e88c1f88"
CLAIM = "(((nontrivial) ∧ (claw_free)) ∧ (triangle_free)) ⇒ edge_cover_number ≤ (2 · min_maximal_matching_number)"


def audit(checkout):
    head = subprocess.check_output(["git", "-C", checkout, "rev-parse", "HEAD"], text=True).strip()
    assert head == PIN
    results = checkout / "results"
    lines = (results / "survivors_by_touch_normalised.txt").read_text().splitlines()
    assert lines[1530] == f"[    39] {CLAIM}    -- promising:class"
    assert sum(CLAIM in line for line in lines) == 1
    records = json.loads((results / "cegis_results.json").read_text())["conjectures"]
    record, = [r for r in records if r["id"] == ROW_ID]
    assert record["status"] == "proposed" and record["lean_proof"] is None and record["statement"] == CLAIM
    for proof in (results / "verified_proofs").glob("*.lean"):
        assert ROW_ID not in proof.read_text() and CLAIM not in proof.read_text()
    files = sorted(results.glob("*refuted.json"))
    assert len(files) == 3
    codes = set()
    for path in files:
        for r in json.loads(path.read_text()):
            assert r.get("id") != ROW_ID and r.get("statement") != CLAIM
            if r.get("witness_g6"):
                codes.add(r["witness_g6"])
    assert all(not w for r in records for w in r.get("tightness_witnesses", []))
    backups = subprocess.check_output(
        ["git", "-C", checkout, "ls-tree", "-r", "HEAD", "--", "results"], text=True
    ).splitlines()
    backups = [line for line in backups if line.endswith("/graphs.g6")]
    assert len(backups) == 4
    blobs = {line.split()[2] for line in backups}
    assert blobs == {"088f28b308df1405d6b63cfd44ec3931c1a9556e"}
    blob, = blobs
    backup = set(subprocess.check_output(
        ["git", "-C", checkout, "cat-file", "blob", blob], text=True
    ).splitlines())

    assert len(codes) == 312 and len(backup) == 4700 and len(codes | backup) == 4776

    from collections import Counter
    stats = Counter()
    raw = subprocess.check_output(["git","-C",checkout,"cat-file","blob",blob],text=True).splitlines()
    for code in sorted(codes|backup):
        g=nx.from_graph6_bytes(code.encode())
        if not (gc.nontrivial(g) and gc.triangle_free(g) and gc.claw_free(g)):
            continue
        stats['antecedent'] += 1
        if list(nx.isolates(g)):
            stats['undefined'] += 1
            continue
        stats['numeric'] += 1
        stats['numeric_from_refutations'] += code in codes
        rho = gc.edge_cover_number(g)
        gamma = gc.min_maximal_matching_number(g)
        assert rho <= 2*gamma
        if nx.is_connected(g):
            stats['connected_numeric'] += 1
            tight = rho == 2*gamma
            assert tight == (len(g) in (3,4,7) and nx.is_isomorphic(g,nx.path_graph(len(g))))
            if tight:
                stats['connected_equality'] += 1
                print("Connected equality: P", len(g), "backup line",
                      raw.index(code)+1 if code in backup else None, "refutation corpus", code in codes)
    assert stats == {"antecedent":414,"undefined":209,"numeric":205,"numeric_from_refutations":35,
                     "connected_numeric":91,"connected_equality":5}
    print("Row 1531; ID e88c1f88; 39 normalized touches; proposed, null proof.")
    print("4776 distinct codes; counts:",dict(stats))
    isolated=nx.empty_graph(2)
    try:
        gc.edge_cover_number(isolated)
    except nx.NetworkXException as e:
        print("Two isolates, GraphCalc:", type(e).__name__, str(e))
    else:
        raise AssertionError("Unexpected numerical value on a graph with isolates")
    # Call the pinned upstream table entry point on actual positive and missing cells.
    import pandas as pd
    sys.path.insert(0, str(checkout))
    from pipeline.invariants_graphcalc import compute_battery
    family=[nx.path_graph(n) for n in (3,4,7)] + [nx.cycle_graph(4),isolated]
    frame=compute_battery(family,workers=1)
    for i,expected in enumerate([(2,1),(2,1),(4,2),(2,2)]):
        assert all(frame.at[i,k] for k in ("nontrivial","claw_free","triangle_free"))
        assert (frame.at[i,"edge_cover_number"],frame.at[i,"min_maximal_matching_number"]) == expected
    assert pd.isna(frame.at[4,"edge_cover_number"])
    print("Pinned battery (cover, edge domination): P3 (2,1), P4 (2,1), P7 (4,2), C4 (2,2); two isolates NaN.")

if __name__ == "__main__":
    assert version("graphcalc") == "2.0.0" and version("networkx") == "3.5"
    audit(Path(sys.argv[1]).resolve())
