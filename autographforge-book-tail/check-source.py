"""Replay AutoGraphForge records and GraphCalc invariants for the three-page book with a tail."""
import argparse
from fractions import Fraction
from itertools import combinations
import json
import math
from pathlib import Path
import subprocess
import sys

import graphcalc.graphs as gc
import networkx as nx


RELEASE = "4d1a8afc99447cacd2328cca20e47b6493e8dbc5"
GRAPHCALC = "ce66ac7390d945885e33f372e29c896fa32e9bc4"
ROWS = (
    (187, 192, "7ca1b1ab", "(((nontrivial) ∧ (chordal)) ∧ (planar)) ⇒ radius ≤ ((2 · slater) + -1)"),
    (221, 231, "0b4cc223", "(((nontrivial) ∧ (chordal)) ∧ (planar)) ⇒ diameter ≤ ((4 · slater) + -2)"),
    (877, 926, "a2ea93c1", "(((nontrivial) ∧ (K_4_free)) ∧ (chordal)) ⇒ radius ≤ ((3/2) · slater)"),
)


def head(checkout):
    return subprocess.check_output(["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()


def release_records(checkout):
    assert head(checkout) == RELEASE
    directory = checkout / "results"
    normalized = (directory / "survivors_by_touch_normalised.txt").read_text().splitlines()
    raw = (directory / "survivors_by_touch.txt").read_text().splitlines()
    data = json.loads((directory / "cegis_results.json").read_text())["conjectures"]
    records = {item["id"]: item for item in data}
    audits = {item["statement"]: item for item in
              json.loads((directory / "audit_top_normalised.json").read_text())["all_ranked"]}
    refutations = json.loads((directory / "cegis_refuted.json").read_text())
    proof_files = list((directory / "verified_proofs").rglob("*.lean"))
    for row, raw_row, ident, statement in ROWS:
        assert normalized[row-1] == raw[raw_row-1]
        assert normalized[row-1].split("] ", 1)[1] == statement + "    -- promising:class"
        record = records[ident]
        assert record["statement"] == statement and record["status"] == "proposed"
        assert record["lean_proof"] is None
        audit = audits[statement]
        assert not audit["decorative"] and audit["known_as"] is None and audit["subsumed_by"] is None
        assert not any(r["id"] == ident or r["statement"] == statement for r in refutations)
        assert all(ident not in (p.name + p.read_text()) for p in proof_files)
        print(f"Normalized {row}, raw {raw_row}, ID {ident}, proposed: {statement}")


def check_witness(checkout):
    assert head(Path(gc.__file__).resolve().parents[3]) == GRAPHCALC
    sys.path.insert(0, str(checkout.resolve()))
    from graphs import invariants
    assert Path(invariants.__file__).resolve().is_relative_to(checkout.resolve())
    g = nx.Graph()
    g.add_nodes_from(range(11))
    g.add_edge(0, 1)
    g.add_edges_from((hub, page) for hub in (0, 1) for page in (2, 3, 4))
    nx.add_path(g, [0, 5, 6, 7, 8, 9, 10])
    assert all(g.has_edge(x, y) == (x < 2 and y < 5 or (x, y) == (0, 5) or 5 <= x and y == x+1)
               for x, y in combinations(g, 2))
    assert all(test(g) for test in (gc.nontrivial, gc.connected, gc.K_4_free, gc.chordal, gc.planar,
                                    invariants.is_chordal, invariants.is_planar))
    sl, rad, diam = gc.slater(g), gc.radius(g), gc.diameter(g)
    assert (sl, rad, diam) == (2, 4, 7)
    assert (invariants.radius(g), invariants.diameter(g)) == (rad, diam)
    assert all(math.isinf(f(nx.empty_graph(2))) for f in (invariants.radius, invariants.diameter))
    print("Degree sequence", sorted((d for _, d in g.degree()), reverse=True))
    print(f"GraphCalc Slater {sl}, radius {rad}, diameter {diam}. All witness graph classes passed.")
    for row, left, right in ((187, rad, 2*sl-1), (221, diam, 4*sl-2), (877, rad, Fraction(3,2)*sl)):
        assert left > right
        print(f"Row {row}: {left} > {right}")


if __name__ == "__main__":
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument("release", type=Path)
    checkout = args.parse_args().release
    release_records(checkout)
    check_witness(checkout)
