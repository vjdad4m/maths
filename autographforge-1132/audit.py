"""Replay the pinned records, audit released inputs and exercise the public battery."""
from collections import Counter
from importlib.metadata import version
from pathlib import Path
import json
import subprocess
import sys

import graphcalc.graphs as gc
import networkx as nx

PIN = "4d1a8afc99447cacd2328cca20e47b6493e8dbc5"
ROWS = {
    1132: ("579ec124", "(((nontrivial) ∧ (subcubic)) ∧ (tree)) ⇒ vertex_clique_cover_number ≤ outer_connected_domination_number",
           "[    58] ", "    -- promising:class", 875),
    5385: ("9f880402", "(outer_connected_domination_number < vertex_clique_cover_number) ⇒ ¬tree",
           "[     -] ", "", 0),
}


def audit(checkout):
    def git(*args):
        return subprocess.check_output(["git", "-C", checkout, *args], text=True)

    assert git("rev-parse", "HEAD").strip() == PIN
    root = checkout / "results"
    lines = (root / "survivors_by_touch_normalised.txt").read_text().splitlines()
    records = json.loads((root / "cegis_results.json").read_text())["conjectures"]
    for idx, (key, claim, prefix, suffix, touches) in ROWS.items():
        assert lines[idx-1] == prefix + claim + suffix
        rec, = [r for r in records if r["id"] == key]
        assert rec["statement"] == claim and rec["status"] == "proposed"
        assert rec["lean_statement"] is None and rec["lean_proof"] is None
        assert rec["metadata"]["touches"] == touches and not any(rec["tightness_witnesses"])
        assert all(key not in f.read_text() and claim not in f.read_text()
                   for f in (root / "verified_proofs").glob("*.lean"))
        print(idx, key, "proposed; source-record touches", touches)
    reports = sorted(root.glob("*refuted.json"))
    assert len(reports) == 3
    refs = set()
    for report in reports:
        for rec in json.loads(report.read_text()):
            assert all(rec.get("id") != key and rec.get("statement") != claim
                       for key, claim, *_ in ROWS.values())
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
        if len(g) < 2 or not gc.tree(g):
            continue
        counts["nontrivial_trees"] += 1
        if not gc.subcubic(g):
            continue
        counts["row_1132_domain"] += 1
        counts["also_in_refutation_files"] += code in refs
        if len(g) <= 8:
            assert gc.vertex_clique_cover_number(g) <= gc.outer_connected_domination_number(g)
            counts["checked_both_optimizers_order_le_8"] += 1
    print("4776 released graph6 encodings", dict(counts))

    sys.path.insert(0, str(checkout))
    from pipeline.invariants_graphcalc import compute_battery
    graphs = [nx.path_graph(5), nx.star_graph(3)]
    for m in range(4):
        g = nx.complete_bipartite_graph(m+2, 2)
        g.remove_edge(0, m+3)
        graphs.append(g)
    cols = ["order", "size", "tree", "subcubic", "vertex_clique_cover_number",
            "outer_connected_domination_number"]
    rows = compute_battery(graphs, workers=1, cap_s=10)
    expected = [(5, 4, True, True, 3, 3), (4, 3, True, True, 3, 3)]
    for m in range(4):
        expected.append((m+4, 2*m+3, m == 0, m+2 <= 3, m+2, 2))
    for name, actual, wanted in zip(["P5","K1,3","rank0","rank1","rank2","rank3"],
                                    rows[cols].itertuples(index=False,name=None), expected):
        assert actual == wanted, (actual, wanted)
        print("compute_battery",name,actual)


if __name__ == "__main__":
    assert version("graphcalc") == "2.0.0" and version("networkx") == "3.5"
    audit(Path(sys.argv[1]).resolve())
