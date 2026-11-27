"""Check both spellings, every released numerical claw-free witness and the public battery."""
import json
import subprocess
import sys
from collections import Counter
from importlib.metadata import version
from pathlib import Path

import graphcalc.graphs as gc
import networkx as nx
import pandas as pd

PIN = "4d1a8afc99447cacd2328cca20e47b6493e8dbc5"
ROWS = {
    5169: ("e2781817", "(min_maximal_matching_number < (((3/5) · edge_cover_number) + -1)) ⇒ ¬claw_free"),
    3060: ("e8bcdcee", "((((5/3) · min_maximal_matching_number) + (5/3)) < edge_cover_number) ⇒ ¬claw_free"),
}
def release(checkout):
    def git(*args):
        return subprocess.check_output(["git", "-C", checkout, *args], text=True)
    assert git("rev-parse", "HEAD").strip() == PIN
    results = checkout / "results"
    lines = (results / "survivors_by_touch_normalised.txt").read_text().splitlines()
    records = json.loads((results / "cegis_results.json").read_text())["conjectures"]
    assert len(lines) == 6634
    assert all(not w for r in records for w in r.get("tightness_witnesses", []))
    for row, (ident, claim) in ROWS.items():
        assert lines[row-1] == "[     -] " + claim and sum(claim in l for l in lines) == 1
        rec, = [r for r in records if r["id"] == ident]
        assert (rec["statement"], rec["status"], rec["generation_method"]) == (claim,"proposed","cegis-graffiti3")
        assert rec["lean_statement"] is None and rec["lean_proof"] is None and rec["metadata"]["touches"] == 0
        for file in (results / "verified_proofs").glob("*.lean"):
            assert ident not in file.read_text() and claim not in file.read_text()
        print(f"{row} {ident}: proposed, zero recorded touches, no Lean statement/proof.")
    refutations = list(results.glob("*refuted.json"))
    assert len(refutations) == 3
    ref = set()
    for p in refutations:
        for r in json.loads(p.read_text()):
            assert all(r.get("id") != ident and r.get("statement") != claim for ident,claim in ROWS.values())
            if r.get("witness_g6"):
                ref.add(r["witness_g6"])
    backups = [l for l in git("ls-tree","-r","HEAD","--","results").splitlines() if l.endswith("/graphs.g6")]
    blobs = {l.split()[2] for l in backups}
    assert len(backups) == 4 and blobs == {"088f28b308df1405d6b63cfd44ec3931c1a9556e"}
    backup = set(git("cat-file","blob",next(iter(blobs))).splitlines())
    assert (len(ref),len(backup),len(ref | backup)) == (312,4700,4776)
    return ref, ref | backup


def chain(k):
    g = nx.path_graph(4*k+1)
    g.add_edges_from((4*i+1,4*i+3) for i in range(k))
    return g


def lower_bound(g):
    # A maximal matching leaves an independent set. Vertex-clique partitions
    # bound its size; one selected edge can dominate at most deg(u)+deg(v)-1
    # edges. Both arguments can be applied componentwise.
    lower = 0
    for vertices in nx.connected_components(g):
        h = g.subgraph(vertices)
        colors = nx.coloring.greedy_color(nx.complement(h),strategy="saturation_largest_first")
        partition_size = 1 + max(colors.values())
        capacity = max(h.degree[u]+h.degree[v]-1 for u,v in h.edges)
        lower += max((len(h)-partition_size+1)//2, (h.number_of_edges()+capacity-1)//capacity,
                     (len(h)+4)//5)
    return lower


def corpus(ref, codes):
    stats = Counter()
    for code in sorted(codes):
        g = nx.from_graph6_bytes(code.encode())
        if not gc.claw_free(g):
            continue
        stats["claw_free"] += 1
        if any(True for _ in nx.isolates(g)):
            stats["missing_cover"] += 1
            continue
        stats["numeric"] += 1
        stats["numeric_from_refutations"] += code in ref
        rho = gc.edge_cover_number(g)
        assert 5*lower_bound(g) >= 3*rho-5, code
    assert stats == {"claw_free":1414,"missing_cover":398,"numeric":1016,"numeric_from_refutations":86}
    print("4776 distinct graph6 encodings:",dict(stats))
    print("No counterexample in the 1016 numerical claw-free encodings.")


def battery(checkout):
    sys.path.insert(0,str(checkout))
    from pipeline.invariants_graphcalc import compute_battery
    graphs = [chain(k) for k in range(1,5)] + [nx.empty_graph(2), nx.disjoint_union(nx.bull_graph(), nx.bull_graph())]
    table = compute_battery(graphs,cap_s=3,max_n=9,workers=1)
    for i,k in enumerate(range(1,5)):
        g = graphs[i]
        assert table.at[i,"claw_free"] and table.at[i,"connected"] and table.at[i,"subcubic"]
        assert table.at[i,"edge_cover_number"] == 2*k+1
        assert table.at[i,"min_maximal_matching_number"] == k
        print(f"k={k}, order={len(g)}, cover={2*k+1}, line domination={k}")
    assert table.at[4,"claw_free"] and pd.isna(table.at[4,"edge_cover_number"])
    assert table.at[5,"claw_free"] and not table.at[5,"connected"]
    assert table.at[5,"edge_cover_number"] == 6 and table.at[5,"min_maximal_matching_number"] == 2
    print("Two isolates: claw-free, missing cover cell. Two disjoint bulls: cover 6, line domination 2.")
    print("13-vertex witness graph6:",nx.to_graph6_bytes(graphs[2],header=False).decode().strip())


if __name__ == "__main__":
    assert version("graphcalc") == "2.0.0" and version("networkx") == "3.5"
    checkout = Path(sys.argv[1]).resolve()
    corpus(*release(checkout))
    battery(checkout)
