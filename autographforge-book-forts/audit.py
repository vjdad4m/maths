"""Audit the pinned records, released graph6 strings and the public GraphCalc battery."""
from collections import Counter
from importlib.metadata import version
from itertools import combinations
from math import comb
from pathlib import Path
import json
import subprocess
import sys
import graphcalc.graphs as gc
import networkx as nx

PIN = "4d1a8afc99447cacd2328cca20e47b6493e8dbc5"
OUT = " ⇒ power_domination_number ≤ sub_total_domination_number"
ROWS = {383: ("69107966", "(((nontrivial) ∧ (connected)) ∧ (planar))" + OUT, 252),
        567: ("b2d82b19", "(((nontrivial) ∧ (chordal)) ∧ (connected))" + OUT, 164)}


def book(k):
    g = nx.Graph([(0, 1)])
    for i in range(k):
        plain, support, leaf1, leaf2 = range(4*i+2, 4*i+6)
        g.add_edges_from([(0, plain), (1, plain), (0, support), (1, support),
                          (support, leaf1), (support, leaf2)])
    return g


def search(g, bound):
    """Return yes with a successful seed, no after exhaustion, or unknown at cap."""
    n = len(g)
    full = (1 << n) - 1
    neighbors = [sum(1 << w for w in g[v]) for v in range(n)]
    closed = [b | (1 << v) for v, b in enumerate(neighbors)]

    def spread(seeds):
        seen = 0
        for v in seeds:
            seen |= closed[v]
        while seen != full:
            add = 0
            active = seen
            while active:
                bit = active & -active
                active ^= bit
                missing = neighbors[bit.bit_length()-1] & ~seen
                if missing and (missing & (missing-1)) == 0:
                    add |= missing
            if not add:
                break
            seen |= add
        return seen

    chosen = []
    observed = 0
    for _ in range(bound):
        candidates = (v for v in range(n) if not observed & (1 << v))
        _, v, observed = max((seen.bit_count(), v, seen) for v in candidates
                              for seen in [spread(chosen+[v])])
        chosen.append(v)
        if observed == full:
            return "yes", chosen
    # Two pendant neighbors of v form a fort. Every successful seed set
    # meets the pair or v. Moving its leaf seed to v enlarges the initial
    # observed set, so these centers can all be required simultaneously.
    required = tuple(v for v in range(n) if sum(g.degree(w) == 1 for w in g[v]) >= 2)
    if len(required) > bound:
        return "no", None
    remaining = sorted(set(range(n)) - set(required))
    budget = bound - len(required)
    if comb(len(remaining), budget) > 1000000:
        return "unknown", None
    for extra in combinations(remaining, budget):
        seeds = required + extra
        if spread(seeds) == full:
            return "yes", seeds
    return "no", None


def audit(checkout):
    def git(*args):
        return subprocess.check_output(["git", "-C", checkout, *args], text=True)
    assert git("rev-parse", "HEAD").strip() == PIN
    root = checkout / "results"
    table = (root / "survivors_by_touch_normalised.txt").read_text().splitlines()
    records = json.loads((root / "cegis_results.json").read_text())["conjectures"]
    reports = sorted(root.glob("*refuted.json"))
    assert len(reports) == 3
    refs = set()
    for row, (ident, claim, touches) in ROWS.items():
        assert table[row-1] == f"[{touches:6}] " + claim + "    -- promising:class"
        r, = [r for r in records if r["id"] == ident]
        assert r["statement"] == claim and r["status"] == "proposed"
        assert r["metadata"]["touches"] == 495 and not any(r["tightness_witnesses"])
        assert r["lean_statement"] is None and r["lean_proof"] is None
        assert all(ident not in p.read_text() and claim not in p.read_text()
                   for p in (root / "verified_proofs").glob("*.lean"))
        for report in reports:
            for r in json.loads(report.read_text()):
                assert r.get("id") != ident and r.get("statement") != claim
                if r.get("witness_g6"):
                    refs.add(r["witness_g6"])
        print(row, ident, "proposed; normalized touches", touches, "record touches 495")
    blobs = {l.split()[2] for l in git("ls-tree", "-r", "HEAD", "--", "results").splitlines()
             if l.endswith("/graphs.g6")}
    assert blobs == {"088f28b308df1405d6b63cfd44ec3931c1a9556e"}
    codes = set(git("cat-file", "blob", blobs.pop()).splitlines())
    assert (len(codes), len(refs), len(codes | refs)) == (4700, 312, 4776)
    by_id = {r["id"]: r for r in json.loads((root / "cegis_refuted.json").read_text())}
    old_code = by_id["b56729d4"]["witness_g6"]
    assert by_id["88925c95"]["witness_g6"] == old_code
    old = nx.from_graph6_bytes(old_code.encode())
    supports = {v for v in old if sum(old.degree(w)==1 for w in old[v]) >= 2}
    assert nx.is_tree(old) and len(old)==32 and gc.sub_total_domination_number(old)==8
    assert len(supports)==10 and gc.is_power_dominating_set(old, supports)
    print("Pastorek tree from b56729d4 and 88925c95: 10 disjoint leaf-fort neighborhoods,"
          " 10 supports power-dominate, sub-total 8")
    counts = Counter()
    for code in sorted(codes | refs):
        g = nx.from_graph6_bytes(code.encode())
        if len(g) < 2 or not nx.is_connected(g):
            continue
        domains = [i for i, predicate in [(383, gc.planar), (567, gc.chordal)] if predicate(g)]
        if not domains:
            continue
        sub = gc.sub_total_domination_number(g)
        answer, seeds = search(g, sub)
        if answer == "yes":
            assert len(seeds) <= sub and gc.is_power_dominating_set(g, set(seeds))
        for row in domains:
            counts[row, answer] += 1
        if answer != "yes":
            print("released", domains, answer, code, "order", len(g), "sub-total", sub,
                  "in_refutation_file", code in refs)
    print("4776 distinct released encodings; row comparison", sorted(counts.items()))
    assert counts == {(383,"no"):1,(383,"yes"):2272,(567,"no"):1,(567,"yes"):1595}
    sys.path.insert(0, str(checkout))
    from pipeline.invariants_graphcalc import compute_battery
    cols = ["order", "nontrivial", "connected", "chordal", "planar",
            "sub_total_domination_number", "power_domination_number"]
    samples = [book(2), book(3)]
    table = compute_battery(samples, workers=1, cap_s=30)
    for k, values in zip([2,3], table[cols].itertuples(index=False, name=None)):
        assert values == (4*k+2, True, True, True, True, 2, k+1)
        print("compute_battery", k, values)


if __name__ == "__main__":
    assert version("graphcalc") == "2.0.0" and version("networkx") == "3.5"
    audit(Path(sys.argv[1]).resolve())
