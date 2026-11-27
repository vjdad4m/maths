"""Recheck Pastorek's pinned record, the released graph6 strings and public battery."""
from collections import Counter
from importlib.metadata import version
from pathlib import Path
import json
import subprocess
import sys

import graphcalc.graphs as gc
import networkx as nx

PIN = "4d1a8afc99447cacd2328cca20e47b6493e8dbc5"
ID = "38975fcb"
CLAIM = "(((nontrivial) ∧ (cograph)) ∧ (eulerian)) ⇒ restrained_domination_number ≤ independent_domination_number"


def audit(checkout):
    def git(*args):
        return subprocess.check_output(["git", "-C", checkout, *args], text=True)

    assert git("rev-parse", "HEAD").strip() == PIN
    root = checkout / "results"
    rows = (root / "survivors_by_touch_normalised.txt").read_text().splitlines()
    assert rows[533] == "[   182] " + CLAIM + "    -- promising:class"
    same = [i for i, row in enumerate(rows, 1) if "⇒ " + CLAIM.split("⇒ ")[1] + "    --" in row]
    assert same == [518, 534] and "(chordal)" in rows[517]
    records = json.loads((root / "cegis_results.json").read_text())["conjectures"]
    rec, = [r for r in records if r["id"] == ID]
    assert rec["statement"] == CLAIM and rec["status"] == "proposed"
    assert rec["metadata"]["touches"] == 2062 and not any(rec["tightness_witnesses"])
    assert rec["lean_statement"] is None and rec["lean_proof"] is None
    assert all(ID not in p.read_text() and CLAIM not in p.read_text()
               for p in (root / "verified_proofs").glob("*.lean"))
    reports = sorted(root.glob("*refuted.json"))
    assert len(reports) == 3
    refs = set()
    for report in reports:
        for r in json.loads(report.read_text()):
            assert r.get("id") != ID and r.get("statement") != CLAIM
            if r.get("witness_g6"):
                refs.add(r["witness_g6"])
    blobs = {l.split()[2] for l in git("ls-tree", "-r", "HEAD", "--", "results").splitlines()
             if l.endswith("/graphs.g6")}
    assert blobs == {"088f28b308df1405d6b63cfd44ec3931c1a9556e"}
    codes = set(git("cat-file", "blob", blobs.pop()).splitlines())
    assert (len(codes), len(refs), len(codes | refs)) == (4700, 312, 4776)
    counts = Counter()
    for code in sorted(codes | refs):
        g = nx.from_graph6_bytes(code.encode())
        if len(g) < 2 or not nx.is_connected(g) or not gc.cograph(g):
            continue
        counts["connected_nontrivial_cographs"] += 1
        counts["row_domain"] += gc.eulerian(g)
        counts["row_domain_in_refutation_graphs"] += gc.eulerian(g) and code in refs
        if len(g) > 10:
            continue
        counts["both_optimizers_order_at_most_10"] += 1
        r = gc.restrained_domination_number(g)
        i = gc.independent_domination_number(g)
        center = next((u for u, d in g.degree if d == len(g) - 1), None)
        expected = 2 if center is None else 1 + sum(d == 1 and v != center for v, d in g.degree)
        leafless = all(d >= 2 for _, d in g.degree)
        assert r == expected and (r <= i) == leafless
        if leafless:
            h = nx.complement(g)
            eq = center is not None or any(not (set(h[u]) & set(h[v])) for u, v in h.edges)
            assert (r == i) == eq
    print("534", ID, "proposed; 182 normalized touches, 2062 record touches; 4776 released graph6 encodings")
    print(dict(counts))
    sys.path.insert(0, str(checkout))
    from pipeline.invariants_graphcalc import compute_battery
    examples = [
        ("P3", nx.path_graph(3), (3, True, True, False, 3, 1)),
        ("K3", nx.complete_graph(3), (3, True, True, True, 1, 1)),
        ("C4", nx.cycle_graph(4), (4, True, True, True, 2, 2)),
        ("K4,4", nx.complete_bipartite_graph(4, 4), (8, True, True, True, 2, 4)),
    ]
    cols = ["order", "nontrivial", "cograph", "eulerian", "restrained_domination_number",
            "independent_domination_number"]
    table = compute_battery([g for _, g, _ in examples], workers=1, cap_s=10)
    for (name, _, expected), values in zip(examples, table[cols].itertuples(index=False, name=None)):
        assert values == expected
        print("compute_battery", name, values)


if __name__ == "__main__":
    assert version("graphcalc") == "2.0.0" and version("networkx") == "3.5"
    audit(Path(sys.argv[1]).resolve())
