"""Verify the physical row, released graph6 data and GraphCalc sample calls."""
import sys
import json
import subprocess
from importlib.metadata import version
from pathlib import Path

import graphcalc.graphs as gc
import networkx as nx

PIN = "4d1a8afc99447cacd2328cca20e47b6493e8dbc5"
ROW_ID = "8a00807b"
CLAIM = "((nontrivial) ∧ (subcubic)) ⇒ edge_cover_number ≤ three_rainbow_domination_number"


def audit(checkout):
    head = subprocess.check_output(["git", "-C", checkout, "rev-parse", "HEAD"], text=True).strip()
    assert head == PIN
    results = checkout / "results"
    lines = (results / "survivors_by_touch_normalised.txt").read_text().splitlines()
    assert lines[1552] == f"[    37] {CLAIM}    -- promising:class"
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
    for code in sorted(codes|backup):
        g=nx.from_graph6_bytes(code.encode())
        if not (gc.nontrivial(g) and gc.subcubic(g)):
            continue
        stats['antecedent'] += 1
        if list(nx.isolates(g)):
            stats['undefined'] += 1
            continue
        stats['numeric'] += 1
        stats['numeric_from_refutations'] += code in codes
        rho = gc.edge_cover_number(g)
        # Each zero has exactly three neighbors, all colored. Zeros form an
        # independent subset of the degree-three subgraph; each matched pair
        # in that subgraph contains at least one colored vertex.
        core = g.subgraph([v for v, degree in g.degree if degree == 3])
        pairs = nx.max_weight_matching(core,maxcardinality=True)
        assert nx.is_matching(core,pairs)
        lower = len(g)-len(core)+len(pairs)
        if rho > lower:
            stats['optimizer_checks'] += 1
            assert rho <= gc.three_rainbow_domination_number(g)
    assert stats == {"antecedent":1174,"undefined":375,"numeric":799,"numeric_from_refutations":103}
    print("Row 1553; ID 8a00807b; 37 normalized touches; proposed, null proof.")
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
    family = [nx.complete_bipartite_graph(3,m) for m in (3,4,7)] + [isolated]
    frame = compute_battery(family,workers=1)
    for i,m in enumerate((3,4,7)):
        assert frame.at[i,"nontrivial"] and bool(frame.at[i,"subcubic"]) == (m==3)
        values = (frame.at[i,"edge_cover_number"],frame.at[i,"three_rainbow_domination_number"])
        assert values == (m,3)
        excess = sum(max(0,d-3) for _,d in family[i].degree)
        assert excess == 3*(m-3) and values[0]-values[1] == excess//3
    assert pd.isna(frame.at[3,"edge_cover_number"])
    print("Pinned battery (cover, singleton three-rainbow): K(3,3) (3,3), K(3,4) (4,3), K(3,7) (7,3); two isolates NaN.")

if __name__ == "__main__":
    assert version("graphcalc") == "2.0.0" and version("networkx") == "3.5"
    audit(Path(sys.argv[1]).resolve())
