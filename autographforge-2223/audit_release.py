"""Check the source row and all released counterexample graph6 strings."""
import json
import sys
from itertools import accumulate, combinations
from pathlib import Path

import networkx as nx

results = Path(sys.argv[1]) / "results"
statement = "((nontrivial) ∧ (K_4_free)) ⇒ triameter ≤ ((4 · sub_total_domination_number) + 4)"
row = (results / "survivors_by_touch_normalised.txt").read_text().splitlines()[2222]
assert row == f"[     8] {statement}    -- promising:class"
record, = (x for x in json.loads((results / "cegis_results.json").read_text())["conjectures"]
           if x["id"] == "00da7483")
assert record["statement"] == statement and record["status"] == "proposed"
assert record["lean_proof"] is None

witnesses = set()
for filename in ("cegis_refuted", "conjecturing_refuted", "property_conjecturing_refuted"):
    for entry in json.loads((results / (filename + ".json")).read_text()):
        assert entry.get("id") != record["id"] and entry.get("statement") != statement
        if entry.get("witness_g6"):
            witnesses.add(entry["witness_g6"])
eligible = 0
for encoded in sorted(witnesses):
    g = nx.from_graph6_bytes(encoded.encode())
    if len(g) < 2 or not nx.is_connected(g) or any(len(c) >= 4 for c in nx.find_cliques(g)):
        continue
    eligible += 1
    degrees = sorted((d for _, d in g.degree()), reverse=True)
    s = next(i for i, total in enumerate(accumulate(degrees), 1) if total >= len(g))
    dist = dict(nx.all_pairs_shortest_path_length(g))
    tri = max((dist[a][b] + dist[b][c] + dist[c][a] for a, b, c in combinations(g, 3)), default=0)
    assert tri <= 4*s+4, encoded

print(f"Physical row 2223, ID {record['id']}, status {record['status']}, proof null.")
print(f"{len(witnesses)} distinct released graph6 witnesses, {eligible} in domain, none refutes row 2223.")
