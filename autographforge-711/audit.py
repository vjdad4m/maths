"""Check the pinned row, released graph6 inputs, and public GraphCalc battery."""
from collections import Counter
from importlib.metadata import version
import json
from pathlib import Path
import subprocess
import sys

import graphcalc.graphs as gc
import networkx as nx

PIN = "4d1a8afc99447cacd2328cca20e47b6493e8dbc5"
ROWS = {
    711: ("2419b925", "((nontrivial) ∧ (eulerian)) ⇒ two_forcing_number ≤ (zero_forcing_number + -1)",
          "[   115] ", "    -- promising:class", 1000),
    6318: ("379aa857", "(two_forcing_number = zero_forcing_number) ⇒ ¬eulerian",
           "[     -] ", "", 0),
}


def main(checkout):
    def git(*args):
        return subprocess.check_output(["git", "-C", checkout, *args], text=True)

    assert git("rev-parse", "HEAD").strip() == PIN
    root = checkout / "results"
    lines = (root / "survivors_by_touch_normalised.txt").read_text().splitlines()
    records = json.loads((root / "cegis_results.json").read_text())["conjectures"]
    refs = set()
    for row, (key, claim, prefix, suffix, touches) in ROWS.items():
        assert lines[row-1] == prefix + claim + suffix
        rec, = [r for r in records if r["id"] == key]
        assert rec["statement"] == claim and rec["status"] == "proposed"
        assert rec["lean_statement"] is None and rec["lean_proof"] is None
        assert rec["metadata"]["touches"] == touches
        assert not any(rec["tightness_witnesses"])
        assert all(key not in f.read_text() and claim not in f.read_text()
                   for f in (root / "verified_proofs").glob("*.lean"))
        print("Pinned row", row, key, rec["status"], "record touches", touches)
    reports = sorted(root.glob("*refuted.json"))
    assert len(reports) == 3
    for f in reports:
        for rec in json.loads(f.read_text()):
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
    stats = Counter()
    singleton = []
    for code in sorted(codes | refs):
        g = nx.from_graph6_bytes(code.encode())
        if len(g) == 1:
            singleton.append((code, code in refs, code in codes))
        if len(g) < 2 or not gc.eulerian(g):
            continue
        assert all(d >= 2 and d % 2 == 0 for _, d in g.degree())
        stats["eligible"] += 1
        stats["in_refutations"] += code in refs
        if len(g) <= 8:
            assert gc.two_forcing_number(g) + 1 <= gc.zero_forcing_number(g)
            stats["optimized_order_at_most_8"] += 1
    print("4776 distinct released encodings", dict(stats))
    print("Single-vertex encodings (code, in refutations, in backups)", singleton)
    sys.path.insert(0, str(checkout))
    from pipeline.invariants_graphcalc import compute_battery

    graphs = [nx.complete_graph(n) for n in (1, 3, 5)] + [nx.path_graph(2)]
    columns = ["order", "nontrivial", "eulerian", "two_forcing_number", "zero_forcing_number"]
    expected = [(1, False, True, 1, 1), (3, True, True, 1, 2),
                (5, True, True, 3, 4), (2, True, False, 1, 1)]
    battery = compute_battery(graphs, workers=1, cap_s=4)
    for name, row, values in zip(["K1", "K3", "K5", "K2"],
                                 battery[columns].itertuples(index=False, name=None), expected):
        print("compute_battery", name, row)
        assert row == values


if __name__ == "__main__":
    assert version("graphcalc") == "2.0.0" and version("networkx") == "3.5"
    main(Path(sys.argv[1]).resolve())
