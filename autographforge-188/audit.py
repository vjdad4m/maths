"""Audit Pastorek's exact row and classify every released graph6 encoding in its domain."""
from collections import Counter
from importlib.metadata import version
import json
from pathlib import Path
import subprocess
import sys

import graphcalc.graphs as gc
import networkx as nx

PIN = "4d1a8afc99447cacd2328cca20e47b6493e8dbc5"
ROW = "((nontrivial) ∧ (cograph)) ⇒ power_domination_number ≤ two_forcing_number"


def verify_component(g):
    # Return a checked ordinary power seed and a matching lower bound on
    # the number of two-forcing seeds needed for the comparison.
    for v in g:
        if gc.is_power_dominating_set(g, {v}):
            return {v}, 1
    assert not any(gc.is_k_forcing_set(g, {v}, 2) for v in g)
    opposite = list(nx.connected_components(nx.complement(g)))
    a, b = next(iter(opposite[0])), next(iter(opposite[1]))
    assert gc.is_power_dominating_set(g, {a,b})
    return {a,b}, 2


def main(root):
    def git(*args):
        return subprocess.check_output(["git","-C",root,*args],text=True).strip()

    assert git("rev-parse","HEAD") == PIN
    results = root / "results"
    rows = (results/"survivors_by_touch_normalised.txt").read_text().splitlines()
    assert rows[187] == "[   548] " + ROW + "    -- promising:class"
    assert all(ROW.split(" ⇒ ")[1] in rows[i-1] and
               rows[i-1].endswith("trivial:subsumed") for i in [195,197,225,228])
    records = json.loads((results/"cegis_results.json").read_text())["conjectures"]
    r, = [rec for rec in records if rec["statement"] == ROW]
    assert r["id"] == "ec83a5d2" and r["status"] == "proposed"
    assert r["metadata"]["touches"] == 1714 and not any(r["tightness_witnesses"])
    assert r["lean_statement"] is None and r["lean_proof"] is None
    for p in (results/"verified_proofs").glob("*.lean"):
        assert ROW not in p.read_text() and r["id"] not in p.read_text()
    refuted = set()
    reports = sorted(results.glob("*refuted.json"))
    assert len(reports) == 3
    for report in reports:
        for entry in json.loads(report.read_text()):
            assert entry.get("id") != r["id"] and entry.get("statement") != ROW
            if entry.get("witness_g6"):
                refuted.add(entry["witness_g6"])
    blobs = {line.split()[2] for line in git("ls-tree","-r","HEAD","--","results").splitlines()
             if line.endswith("/graphs.g6")}
    assert blobs == {"088f28b308df1405d6b63cfd44ec3931c1a9556e"}
    backup = set(git("cat-file","blob",blobs.pop()).splitlines())
    assert (len(backup),len(refuted),len(backup | refuted)) == (4700,312,4776)
    print("Physical row 188, ec83a5d2, proposed. Normalized touches 548, CEGIS touches 1714.")
    counts = Counter()
    for code in sorted(backup | refuted):
        g = nx.from_graph6_bytes(code.encode())
        if not gc.nontrivial(g) or not gc.cograph(g):
            continue
        parts = list(nx.connected_components(g))
        seed, lower = set(), 0
        for part in parts:
            subset, cost = verify_component(g.subgraph(part).copy())
            seed.update(subset)
            lower += cost
        assert len(seed) <= lower and gc.is_power_dominating_set(g, seed)
        counts["eligible"] += 1
        counts["disconnected"] += len(parts)>1
        counts["with isolates"] += nx.number_of_isolates(g)>0
        counts["in refutation files"] += code in refuted
        counts["needs two in a component"] += lower>len(parts)
    print("4776 distinct released encodings, exhaustive row-domain check", sorted(counts.items()))
    sys.path.insert(0,str(root))
    from pipeline.invariants_graphcalc import compute_battery
    k = nx.complete_bipartite_graph(3,3)
    cone = nx.complete_graph(1)
    cone = nx.full_join(cone,nx.path_graph(4),rename=("hub","path"))
    graphs = [k,nx.disjoint_union(k,nx.empty_graph(2)),cone]
    columns = ["order","nontrivial","connected","cograph","power_domination_number","two_forcing_number"]
    rows = list(compute_battery(graphs,workers=1,cap_s=30)[columns].itertuples(index=False,name=None))
    assert rows == [(6,True,True,True,2,2),(8,True,False,True,4,4),(5,True,True,False,1,1)]
    assert gc.k_forcing_number(k,3) == 1
    print("Public battery (order, nontrivial, connected, cograph, power, two-forcing)", rows)
    print("K3,3 three-forcing number 1")


if __name__ == "__main__":
    assert version("networkx") == "3.5" and version("graphcalc") == "2.0.0"
    main(Path(sys.argv[1]).resolve())
