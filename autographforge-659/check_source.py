"""Verify the physical row, released graph6 data and GraphCalc sample calls."""
import sys
import json
from collections import Counter
import subprocess
from importlib.metadata import version
from pathlib import Path

import graphcalc.graphs as gc
import networkx as nx

PIN = "4d1a8afc99447cacd2328cca20e47b6493e8dbc5"
ROW_ID = "2763b0fb"
CLAIM = "(((nontrivial) ∧ (planar)) ∧ (triangle_free)) ⇒ (min_maximal_matching_number + 1) ≤ roman_domination_number"


def audit(checkout):
    head = subprocess.check_output(["git", "-C", checkout, "rev-parse", "HEAD"], text=True).strip()
    assert head == PIN
    results = checkout / "results"
    lines = (results / "survivors_by_touch_normalised.txt").read_text().splitlines()
    assert lines[658] == f"[   136] {CLAIM}    -- promising:class"
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

    import random
    rng = random.Random(659)
    counts = Counter()
    failures = []
    for code in sorted(codes | backup, key=lambda x: (len(x), x)):
        g = nx.from_graph6_bytes(code.encode())
        if not (gc.nontrivial(g) and gc.triangle_free(g) and nx.check_planarity(g)[0]):
            continue
        counts["eligible"] += 1
        counts["eligible_from_refutations"] += code in codes
        # Every greedy maximal matching is itself an edge-dominating set.
        edges = list(g.edges())
        upper = len(g)
        for _ in range(8):
            used = set()
            for a, b in edges:
                if a not in used and b not in used:
                    used.update((a, b))
            upper = min(upper, len(used) // 2)
            rng.shuffle(edges)
        roman = gc.roman_domination_number(g)
        if upper + 1 <= roman:
            continue
        matching = gc.min_maximal_matching_number(g)
        if matching + 1 > roman:
            failures.append((code, len(g), matching, roman))
    assert counts == {"eligible": 957, "eligible_from_refutations": 115}
    assert not failures
    print("Physical row 659, ID 2763b0fb, proposed, 136 touches, null proof.")
    print("4776 distinct released encodings;", dict(counts))
    print("Eligible released counterexamples:", failures)


def theta(k):
    g = nx.Graph()
    for i in range(k):
        g.add_edges_from([(0, 2*i+2), (2*i+2, 2*i+3), (2*i+3, 1)])
    return g


if __name__ == "__main__":
    assert version("graphcalc") == "2.0.0" and version("networkx") == "3.5"
    audit(Path(sys.argv[1]).resolve())
    for k in (2, 3, 4, 7):
        g = theta(k)
        assert gc.nontrivial(g) and gc.planar(g) and gc.triangle_free(g)
        values = (gc.min_maximal_matching_number(g), gc.roman_domination_number(g))
        assert values == (k, 4)
        print(f"order {len(g)}, k={k}, matching and Roman {values}")
