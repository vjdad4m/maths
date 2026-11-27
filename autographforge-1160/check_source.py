"""Check the pinned row, its released witness corpus and the two GraphCalc values."""
import argparse
import json
from collections import Counter
import subprocess
from importlib.metadata import version
from pathlib import Path

import graphcalc.graphs as gc
import networkx as nx

PIN = "4d1a8afc99447cacd2328cca20e47b6493e8dbc5"
ROW_ID = "4e044e85"
CLAIM = "(((nontrivial) ∧ (cubic)) ∧ (triangle_free)) ⇒ vertex_clique_cover_number ≤ annihilation_number"


def audit(checkout):
    head = subprocess.check_output(["git", "-C", checkout, "rev-parse", "HEAD"], text=True).strip()
    assert head == PIN
    results = checkout / "results"
    lines = (results / "survivors_by_touch_normalised.txt").read_text().splitlines()
    assert lines[1159] == f"[    52] {CLAIM}    -- promising:class"
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
    counts = Counter()
    for code in sorted(codes | backup):
        g = nx.from_graph6_bytes(code.encode())
        if not gc.nontrivial(g) or not gc.cubic(g):
            continue
        counts["cubic"] += 1
        counts["refuted_cubic"] += code in codes
        if not gc.triangle_free(g):
            continue
        counts["eligible"] += 1
        counts["refuted_eligible"] += code in codes
        pairs = nx.max_weight_matching(g, maxcardinality=True)
        assert nx.is_perfect_matching(g, pairs)
        assert len(pairs) == gc.annihilation_number(g)
    assert (len(codes), counts["refuted_cubic"], counts["refuted_eligible"]) == (312, 31, 16)
    assert (len(backup), len(codes | backup), counts["cubic"], counts["eligible"]) == (4700, 4776, 118, 56)
    print("Row 1160, ID 4e044e85, proposed, 52 touches, null proof.")
    print("Three refutation files: 312 distinct witness encodings, 31 cubic, 16 eligible.")
    print("Including four identical 4700-graph backups: 4776 distinct encodings, 118 cubic, 56 eligible.")
    print("All 56 eligible graphs have checked perfect matchings of size equal to their annihilation number.")


def witness(full_milp):
    g = nx.Graph()
    for i in range(3):
        def v(u):
            return 1 + 7*i + u
        for a in (1, 2, 3):
            for b in (4, 5, 6):
                if (a,b) != (1,4):
                    g.add_edge(v(a),v(b))
        g.add_edges_from([(v(1),v(0)), (v(0),v(4)), (0,v(0))])
    assert gc.nontrivial(g) and gc.connected(g) and gc.cubic(g) and gc.triangle_free(g)
    assert (len(g),g.number_of_edges()) == (22,33)
    # A clique cannot meet two components after deleting the hub. Use the
    # original cover optimizer for these lower bounds, then check an explicit
    # partition of the full graph to attain their sum.
    lobes = list(nx.connected_components(g.subgraph(set(g) - {0})))
    lower = sum(gc.vertex_clique_cover_number(g.subgraph(c).copy()) for c in lobes)
    partition = []
    for i in range(3):
        root = 1 + 7*i
        partition.append([root, 0] if i == 0 else [root])
        partition.extend([[root+a, root+b] for a,b in [(1,5),(2,6),(3,4)]])
    flat = [v for block in partition for v in block]
    assert len(flat) == len(set(flat)) == len(g) and set(flat) == set(g)
    assert all(g.has_edge(*block) for block in partition if len(block) == 2)
    cover = len(partition)
    assert cover == lower
    annihilation = gc.annihilation_number(g)
    assert (cover, annihilation) == (12,11)
    matching = nx.max_weight_matching(g, maxcardinality=True)
    assert nx.is_matching(g,matching) and len(matching) == 10
    print(f"Connected cubic triangle-free witness, order 22, size 33, clique cover {cover} (GraphCalc lobe optima and partition), GraphCalc annihilation {annihilation}.", flush=True)
    if full_milp:
        assert gc.vertex_clique_cover_number(g) == cover
        print("GraphCalc full-graph clique-cover MILP returned 12.", flush=True)


if __name__ == "__main__":
    assert version("graphcalc") == "2.0.0" and version("networkx") == "3.5"
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    parser.add_argument("--full-milp", action="store_true", help="also solve the symmetric 22-vertex coloring MILP")
    args = parser.parse_args()
    audit(args.checkout.resolve())
    witness(args.full_milp)
