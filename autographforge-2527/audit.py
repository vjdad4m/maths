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
ROW_ID = "1bc05f9a"
CLAIM = "((nontrivial) ∧ (bipartite)) ⇒ min_maximal_matching_number ≤ (((3/4) · independent_domination_number) + (11/2))"


def crown_data(g):
    if len(g) < 6 or not nx.is_connected(g):
        return None
    left, right = nx.bipartite.sets(g)
    side = len(left)
    if len(right) != side or any(g.degree(v) != side - 1 for v in g):
        return None
    # Use the same index for each nonedge across the parts. This is an
    # explicit isomorphism with the crown family formalized in Crown.lean.
    left_order = sorted(left)
    right_order = [next(iter(right - set(g[u]))) for u in left_order]
    assert set(right_order) == right
    assert all(g.has_edge(u,v) == (i != j) for i,u in enumerate(left_order)
               for j,v in enumerate(right_order))
    a = min(left)
    b, = right - set(g[a])
    assert nx.is_dominating_set(g, {a,b}) and not g.has_edge(a,b)
    rem = g.subgraph(set(g)-{a,b})
    matching = nx.bipartite.maximum_matching(rem, top_nodes=left-{a})
    assert len(matching) == len(rem)
    # The two unmatched vertices are nonadjacent, so this matching is maximal.
    # The triangle-free minimum-degree lower bound (row 1078) gives equality.
    return side - 1, 2


def upper_matching(g, edges, rng):
    upper = len(g)
    for _ in range(40):
        used = set()
        for a,b in edges:
            if a not in used and b not in used:
                used.update((a,b))
        upper = min(upper,len(used)//2)
        rng.shuffle(edges)
    return upper


def saturates(vertex_mask, allowed, neighbors):
    """Test whether all marked vertices can receive distinct allowed neighbors."""
    assigned = {}

    def augment(v, seen):
        choices = neighbors[v] & allowed
        while choices:
            bit = choices & -choices
            choices -= bit
            if bit in seen:
                continue
            seen.add(bit)
            old = assigned.get(bit)
            if old is None or augment(old, seen):
                assigned[bit] = v
                return True
        return False

    while vertex_mask:
        bit = vertex_mask & -vertex_mask
        vertex_mask -= bit
        if not augment(bit.bit_length()-1, set()):
            return False
    return True


def feasible_matching(g, target):
    """Exact bipartite test for a maximal matching of size at most target."""
    color = nx.bipartite.color(g)
    left, right = ([v for v in g if color[v] == c] for c in (0, 1))
    if len(left) > len(right):
        left, right = right, left
    if len(left) <= target:
        return True
    left.sort(key=lambda v: (-g.degree(v), v))
    right.sort()
    def incidences(source, dest):
        bit = {v:1 << i for i, v in enumerate(dest)}
        return [sum(bit[v] for v in g[u]) for u in source]

    lr = incidences(left, right)
    rl = incidences(right, left)
    all_left = (1 << len(left))-1
    all_right = (1 << len(right))-1
    full = saturates(all_left, all_right, lr)
    if not full:
        maximum = nx.bipartite.maximum_matching(g, top_nodes=left)
        if len(maximum)//2 <= target:
            return True

    # U is the unmatched subset on the left. A size-target maximal matching
    # saturates L-U and every vertex of N(U). First match N(U) into L-U,
    # then augment without uncovering N(U) until all of L-U is matched.
    def search(first, need, excluded, required):
        if required.bit_count() > target:
            return False
        if not need:
            remaining = all_left ^ excluded
            return (saturates(required, remaining, rl)
                    and (full or saturates(remaining, all_right, lr)))
        for j in range(first, len(left)-need+1):
            if search(j+1, need-1, excluded | (1 << j), required | lr[j]):
                return True
        return False

    return search(0, len(left)-target, 0, 0)


def audit(checkout):
    head = subprocess.check_output(["git", "-C", checkout, "rev-parse", "HEAD"], text=True).strip()
    assert head == PIN
    results = checkout / "results"
    lines = (results / "survivors_by_touch_normalised.txt").read_text().splitlines()
    assert lines[2526] == f"[     4] {CLAIM}    -- promising:class"
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
    rng = random.Random(2527)
    archived = subprocess.check_output(
        ["git","-C",checkout,"cat-file","blob",blob],text=True).splitlines()[1123]
    assert archived == r"QsaCCA?^r|Nk]w\wL{A~?Nw??^w"
    assert crown_data(nx.from_graph6_bytes(archived.encode())) == (8,2)
    counts = Counter()
    failures = []
    for code in sorted(codes | backup, key=lambda x: (len(x), x)):
        g = nx.from_graph6_bytes(code.encode())
        if not (gc.nontrivial(g) and gc.bipartite(g)):
            continue
        counts["eligible"] += 1
        counts["eligible_from_refutations"] += code in codes
        crown = crown_data(g)
        if crown is not None:
            matching, independent = crown
            counts["crowns"] += 1
            if 4*matching > 3*independent+22:
                failures.append((len(g), "crown", matching, independent, code in codes, nx.check_planarity(g)[0]))
            continue
        edges = list(g.edges())
        upper = upper_matching(g, edges, rng)
        if 4*upper <= 3*gc.slater(g)+22:
            counts["degree_certificate"] += 1
            continue
        independent = gc.independent_domination_number(g)
        target = (3*independent+22)//4
        if upper <= target:
            counts["independent_optimizer"] += 1
            continue
        biggest = max(g.degree(a)+g.degree(b)-1 for a,b in edges)
        lower = max(min(d for _,d in g.degree()), (len(edges)+biggest-1)//biggest)
        if lower > target:
            counts["degree_refutation"] += 1
            failures.append((len(g), "lower bound", lower, independent, code in codes, nx.check_planarity(g)[0]))
            continue
        answer = feasible_matching(g,target)
        counts[{True:"matching_exists",False:"matching_infeasible"}[answer]] += 1
        if answer is False:
            failures.append((len(g), "lower bound", target+1, independent, code in codes, nx.check_planarity(g)[0]))
    assert counts["eligible"] == 1223 and counts["eligible_from_refutations"] == 159
    assert len(failures) == 54 and sum(r[4] for r in failures) == 11
    assert not any(r[5] for r in failures)
    assert sum(r[1]=="crown" for r in failures) == 15
    print("Physical row 2527, ID 1bc05f9a, proposed, four touches, null proof.")
    print("4776 distinct released encodings;", dict(counts))
    print("Violating crowns (order, type, matching, independent domination, "
          "in named refutation files, planar):", [r for r in failures if r[1]=="crown"])
    print("Additional violations by edge lower bound:", [r for r in failures if r[1]!="crown"])


def theta(k):
    g = nx.Graph()
    for i in range(k):
        g.add_edges_from([(0, 2*i+2), (2*i+2, 2*i+3), (2*i+3, 1)])
    return g


def check_matching_test():
    """Cross-check against all matchings for every labeled subgraph of K₃,₃."""
    from itertools import combinations
    board = list(nx.complete_bipartite_graph(3,3).edges())
    for mask in range(1 << len(board)):
        g = nx.Graph()
        g.add_nodes_from(range(6))
        edges = [e for i,e in enumerate(board) if (mask >> i) & 1]
        g.add_edges_from(edges)
        oracle = next(k for k in range(4) if any(
            nx.is_maximal_matching(g,picked) for picked in combinations(edges,k)))
        assert all(feasible_matching(g,k) == (oracle <= k) for k in range(4))
    print("Matching feasibility agrees with exhaustive search on all 512 subgraphs of K3,3.")


if __name__ == "__main__":
    assert version("graphcalc") == "2.0.0" and version("networkx") == "3.5"
    check_matching_test()
    audit(Path(sys.argv[1]).resolve())
    for k in (1, 2, 7, 8, 12):
        graph = theta(k)
        assert gc.nontrivial(graph) and gc.bipartite(graph) and gc.planar(graph)
        result = (gc.min_maximal_matching_number(graph), gc.independent_domination_number(graph))
        assert result == (k, 2)
        print(f"order {len(graph)}, k={k}, matching and independent domination {result}")
