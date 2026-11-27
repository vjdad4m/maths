"""Audit the exact proposed record, all released encodings, and GraphCalc's public battery."""
import json
from collections import Counter
from importlib.metadata import version
from pathlib import Path
import subprocess
import sys

import graphcalc.graphs as gc
import networkx as nx

PIN = "4d1a8afc99447cacd2328cca20e47b6493e8dbc5"
CLAIM = "(((nontrivial) ∧ (chordal)) ∧ (cograph)) ⇒ domination_number ≤ power_domination_number"


def main(root):
    def git(*args):
        return subprocess.check_output(["git", "-C", root, *args], text=True).strip()

    assert git("rev-parse", "HEAD") == PIN
    results = root / "results"
    rows = (results / "survivors_by_touch_normalised.txt").read_text().splitlines()
    assert rows[104] == "[   888] " + CLAIM + "    -- promising:class"
    records = json.loads((results / "cegis_results.json").read_text())["conjectures"]
    r, = [entry for entry in records if entry["statement"] == CLAIM]
    assert r["id"] == "516f48da" and r["status"] == "proposed"
    assert r["metadata"]["touches"] == 1399 and not any(r["tightness_witnesses"])
    assert r["lean_proof"] is None and r["lean_statement"] is None
    for p in (results / "verified_proofs").glob("*.lean"):
        assert CLAIM not in p.read_text() and r["id"] not in p.read_text()
    refs = set()
    reports = sorted(results.glob("*refuted.json"))
    assert len(reports) == 3
    for report in reports:
        for entry in json.loads(report.read_text()):
            assert entry.get("statement") != CLAIM and entry.get("id") != r["id"]
            if entry.get("witness_g6"):
                refs.add(entry["witness_g6"])
    blobs = {line.split()[2] for line in git("ls-tree", "-r", "HEAD", "--", "results").splitlines()
             if line.endswith("/graphs.g6")}
    assert blobs == {"088f28b308df1405d6b63cfd44ec3931c1a9556e"}
    backup = set(git("cat-file", "blob", blobs.pop()).splitlines())
    assert (len(backup),len(refs),len(backup | refs)) == (4700,312,4776)
    print("Physical row 105, CEGIS 516f48da, proposed. Normalized touches 888, raw touches 1399.")
    counts = Counter()
    for code in sorted(backup | refs):
        g = nx.from_graph6_bytes(code.encode())
        if not (gc.nontrivial(g) and gc.chordal(g) and gc.cograph(g)):
            continue
        parts = list(nx.connected_components(g))
        centers = {next(v for v in part if g.degree(v) == len(part)-1) for part in parts}
        assert len(centers) == len(parts) and gc.is_dominating_set(g,centers)
        assert gc.is_power_dominating_set(g,centers)
        counts["qualifying"] += 1
        counts["disconnected"] += len(parts)>1
        counts["with isolates"] += nx.number_of_isolates(g)>0
        counts["in prior refutations"] += code in refs
    print("All 4776 distinct released encodings inspected. Certified a center per component",sorted(counts.items()))

    assert gc.power_domination_number(nx.empty_graph(0)) is None
    print("Empty graph outside catalogue domain: GraphCalc power_domination_number returns None.")
    sys.path.insert(0,str(root))
    from pipeline.invariants_graphcalc import compute_battery
    graphs = [nx.path_graph(4),nx.cycle_graph(4),nx.disjoint_union(nx.star_graph(3),nx.empty_graph(2)),
              nx.full_join(nx.complete_graph(1),nx.path_graph(4),rename=("hub","path"))]
    fields = ["order","chordal","cograph","domination_number","power_domination_number"]
    output = list(compute_battery(graphs,workers=1,cap_s=30)[fields].itertuples(index=False,name=None))
    assert output == [(4,True,False,2,1),(4,False,True,2,1),(6,True,True,3,3),(5,True,False,1,1)]
    print("Battery on P4, C4, claw plus two isolates, cone over P4",output)


if __name__ == "__main__":
    assert version("networkx") == "3.5" and version("graphcalc") == "2.0.0"
    main(Path(sys.argv[1]).resolve())
