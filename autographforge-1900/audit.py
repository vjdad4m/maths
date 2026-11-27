"""Audit physical row 1900 and run the upstream battery on test graphs."""
from collections import Counter
from importlib.metadata import version
from pathlib import Path
import json
import subprocess
import sys
import graphcalc.graphs as gc
import networkx as nx

PIN = "4d1a8afc99447cacd2328cca20e47b6493e8dbc5"
ID = "044250a9"
CLAIM = "(((nontrivial) ∧ (eulerian)) ∧ (triangle_free)) ⇒ outer_connected_domination_number ≤ ((2 · vertex_clique_cover_number) + -2)"


def run(checkout):
    def git(*args):
        return subprocess.check_output(["git", "-C", checkout, *args], text=True)

    assert git("rev-parse", "HEAD").strip() == PIN
    root = checkout / "results"
    table = (root / "survivors_by_touch_normalised.txt").read_text().splitlines()
    assert table[1899] == "[    20] " + CLAIM + "    -- promising:class"
    records = json.loads((root / "cegis_results.json").read_text())["conjectures"]
    rec, = [r for r in records if r["id"] == ID]
    assert rec["statement"] == CLAIM and rec["status"] == "proposed"
    assert rec["metadata"]["touches"] == 311 and not any(rec["tightness_witnesses"])
    assert rec["lean_statement"] is None and rec["lean_proof"] is None
    assert all(ID not in f.read_text() and CLAIM not in f.read_text()
               for f in (root / "verified_proofs").glob("*.lean"))
    print("1900", ID, "proposed; normalized touches 20; record touches 311")
    reports = sorted(root.glob("*refuted.json"))
    assert len(reports) == 3
    refs = set()
    for report in reports:
        for rec in json.loads(report.read_text()):
            assert rec.get("id") != ID and rec.get("statement") != CLAIM
            if rec.get("witness_g6"):
                refs.add(rec["witness_g6"])
    backups = [l for l in git("ls-tree", "-r", "HEAD", "--", "results").splitlines()
               if l.endswith("/graphs.g6")]
    blob = "088f28b308df1405d6b63cfd44ec3931c1a9556e"
    assert len(backups) == 4 and {l.split()[2] for l in backups} == {blob}
    codes = set(git("cat-file", "blob", blob).splitlines())
    assert (len(codes), len(refs), len(codes | refs)) == (4700, 312, 4776)
    counts = Counter()
    for code in sorted(codes | refs):
        g = nx.from_graph6_bytes(code.encode())
        if len(g) < 2 or not gc.eulerian(g) or not gc.triangle_free(g):
            continue
        counts["row_domain"] += 1
        counts["also_in_refutations"] += code in refs
        v = max(g, key=lambda x: g.degree(x))
        w = next(iter(g[v]))
        outside = {v} | (set(g[v]) - {w})
        chosen = set(g) - outside
        assert len(chosen) + g.degree(v) == len(g)
        assert nx.is_connected(g.subgraph(outside)) and all(set(g[x]) & chosen for x in outside)
        if len(g) <= 10:
            theta = gc.vertex_clique_cover_number(g)
            outer = gc.outer_connected_domination_number(g)
            assert outer <= len(chosen) and outer + 2 <= 2*theta
            perfect = 2*len(nx.max_weight_matching(g, maxcardinality=True)) == len(g)
            assert (outer + 2 == 2*theta) == (g.degree(v) == 2 and perfect)
            counts["both_optimizers_order_le_10"] += 1
    print("4776 distinct encodings; explicit star certificate on all eligible graphs", dict(counts))

    sys.path.insert(0, str(checkout))
    from pipeline.invariants_graphcalc import compute_battery
    graphs = [nx.cycle_graph(4), nx.cycle_graph(5), nx.cycle_graph(6),
              nx.complete_bipartite_graph(2,4), nx.complete_bipartite_graph(2,6)]
    cols = ["order","nontrivial","eulerian","triangle_free","maximum_degree",
            "vertex_clique_cover_number","outer_connected_domination_number"]
    table = compute_battery(graphs,workers=1,cap_s=10)
    expected = [(4,2,2,2),(5,2,3,3),(6,2,3,4),(6,4,4,2),(8,6,6,2)]
    for name, (n,d,t,o), row in zip(["C4","C5","C6","K2,4","K2,6"],
                                    expected,table[cols].itertuples(index=False,name=None)):
        assert row == (n,True,True,True,d,t,o)
        print("compute_battery",name,row)


if __name__ == "__main__":
    assert version("graphcalc") == "2.0.0" and version("networkx") == "3.5"
    run(Path(sys.argv[1]).resolve())
