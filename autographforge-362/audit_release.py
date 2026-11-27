"""Check row numbering/status and test the released refutation witnesses for reuse."""
import json
import sys
from itertools import accumulate
from pathlib import Path

import networkx as nx

results = Path(sys.argv[1]) / "results"
statement = "((nontrivial) ∧ (triangle_free)) ⇒ burning_number ≤ ((3/2) · sub_total_domination_number)"
row = (results / "survivors_by_touch_normalised.txt").read_text().splitlines()[361]
assert row == f"[   276] {statement}    -- promising:class"
record, = (c for c in json.loads((results / "cegis_results.json").read_text())["conjectures"]
           if c["id"] == "1be64126")
assert record["statement"] == statement and record["status"] == "proposed"
assert record["lean_proof"] is None
witnesses = set()
for filename in ["cegis_refuted", "conjecturing_refuted", "property_conjecturing_refuted"]:
    for entry in json.loads((results / f"{filename}.json").read_text()):
        assert entry.get("statement") != statement and entry.get("id") != record["id"]
        if entry.get("witness_g6"):
            witnesses.add(entry["witness_g6"])

def covered_within(graph, k):
    """Search for k balls of radii k-1,...,0 that cover every vertex."""
    if nx.is_connected(graph) and nx.radius(graph) + 1 <= k:
        return True
    distances = dict(nx.all_pairs_shortest_path_length(graph))
    balls = [
        {sum(1 << w for w, d in distances[v].items() if d <= r) for v in graph}
        for r in reversed(range(k))
    ]
    full = (1 << len(graph)) - 1

    def search(i, mask):
        if mask == full:
            return True
        if i == k:
            return False
        options = sorted(balls[i], key=lambda b: (b & ~mask).bit_count(), reverse=True)
        return any(search(i+1, mask | b) for b in options)

    return search(0, 0)

for encoded in sorted(witnesses):
    g = nx.from_graph6_bytes(encoded.encode())
    if len(g) < 2 or any(nx.triangles(g).values()):
        continue
    degrees = sorted((d for _, d in g.degree()), reverse=True)
    s = next((i for i, total in enumerate(accumulate(degrees), 1) if total >= len(g)), None)
    if s is not None:
        assert covered_within(g, 3*s//2), encoded

print(f"Physical row 362, ID {record['id']}, status {record['status']}, no release proof.")
print(f"Checked {len(witnesses)} distinct released graph6 witnesses; none refutes row 362.")
