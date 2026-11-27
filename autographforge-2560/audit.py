"""Verify the physical row, released graph6 data and GraphCalc sample calls."""
import sys
import json
import subprocess
from importlib.metadata import version
from pathlib import Path

import graphcalc.graphs as gc
import networkx as nx

PIN = "4d1a8afc99447cacd2328cca20e47b6493e8dbc5"
ROW_ID = "6d159443"
CLAIM = "(((nontrivial) ∧ (chordal)) ∧ (claw_free)) ⇒ edge_cover_number ≤ (3 · min_maximal_matching_number)"


def audit(checkout):
    head = subprocess.check_output(["git", "-C", checkout, "rev-parse", "HEAD"], text=True).strip()
    assert head == PIN
    results = checkout / "results"
    lines = (results / "survivors_by_touch_normalised.txt").read_text().splitlines()
    assert lines[2559] == f"[     3] {CLAIM}    -- promising:class"
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
        if len(g) in (4,5):
            for name,h in (("claw",nx.star_graph(3)),("bull",nx.bull_graph())):
                if nx.is_isomorphic(g,h):
                    print(name, "backup line", raw.index(code)+1 if code in backup else None, "refutation corpus",code in codes)
        if not (gc.nontrivial(g) and gc.chordal(g) and gc.claw_free(g)):
            continue
        stats['antecedent'] += 1
        if list(nx.isolates(g)):
            stats['undefined'] += 1
            continue
        stats['numeric'] += 1
        stats['numeric_from_refutations'] += code in codes
        rho = gc.edge_cover_number(g)
        # Each selected edge uv meets deg(u)+deg(v)-1 edges. Sum
        # componentwise ceilings to obtain a lower bound on edge domination.
        lower=0
        for comp in nx.connected_components(g):
            h=g.subgraph(comp)
            cap=max(h.degree(a)+h.degree(b)-1 for a,b in h.edges)
            lower+=(h.number_of_edges()+cap-1)//cap
        if rho > 3*lower:
            stats['optimizer_checks']+=1
            assert rho <= 3*gc.min_maximal_matching_number(g)
    assert stats == {"antecedent":953,"undefined":354,"numeric":599,"numeric_from_refutations":37}
    assert gc.chordal(nx.bull_graph()) and gc.claw_free(nx.bull_graph())
    assert (gc.edge_cover_number(nx.bull_graph()),gc.min_maximal_matching_number(nx.bull_graph())) == (3,1)
    print("Row 2560; ID 6d159443; 3 normalized touches; proposed, null proof.")
    print("4776 distinct codes; counts:",dict(stats))
    for name,h in (("triangle",nx.complete_graph(3)),("claw",nx.star_graph(3)),("bull",nx.bull_graph())):
        print(name,gc.edge_cover_number(h),gc.min_maximal_matching_number(h))
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
    frame=compute_battery([nx.complete_graph(3),isolated,nx.bull_graph()],workers=1)
    key="edge_cover_number"
    assert frame.at[0,key] == 2 and pd.isna(frame.at[1,key])
    assert frame.at[2,key] == 3 and frame.at[2,"min_maximal_matching_number"] == 1
    assert frame.at[2,"chordal"] and frame.at[2,"claw_free"] and frame.at[2,"nontrivial"]
    print("Pinned compute_battery: triangle edge cover 2; two isolates NaN; bull eligible with values 3, 1.")

if __name__ == "__main__":
    assert version("graphcalc") == "2.0.0" and version("networkx") == "3.5"
    audit(Path(sys.argv[1]).resolve())
