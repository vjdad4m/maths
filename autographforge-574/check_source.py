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
ROW_ID = "07b76d4b"
CLAIM = "(((nontrivial) ∧ (eulerian)) ∧ (triangle_free)) ⇒ domination_number ≤ min_maximal_matching_number"


def audit(checkout):
    head = subprocess.check_output(["git", "-C", checkout, "rev-parse", "HEAD"], text=True).strip()
    assert head == PIN
    results = checkout / "results"
    lines = (results / "survivors_by_touch_normalised.txt").read_text().splitlines()
    assert lines[573] == f"[   163] {CLAIM}    -- promising:class"
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
    import random
    rng = random.Random(574)
    for code in sorted(codes | backup):
        g = nx.from_graph6_bytes(code.encode())
        if not (gc.nontrivial(g) and gc.eulerian(g) and gc.triangle_free(g)):
            continue
        counts["eligible"] += 1
        counts["refuted_eligible"] += code in codes
        edges = list(g.edges())
        volume = max(g.degree[a]+g.degree[b]-1 for a,b in edges)
        lower = max(min(d for _,d in g.degree), (len(edges)+volume-1)//volume)
        neighborhoods = {v:{v,*g[v]} for v in g}
        for _ in range(40):
            uncovered=set(g); selected=set()
            order=list(g);rng.shuffle(order)
            while uncovered:
                v=max(order,key=lambda v:len(uncovered & neighborhoods[v]))
                selected.add(v);uncovered-=neighborhoods[v]
            if len(selected)<=lower: break
        if len(selected)>lower:
            selected=gc.minimum_dominating_set(g)
        assert nx.is_dominating_set(g,selected)
        if len(selected)<=lower:
            counts["degree_or_volume"]+=1
            continue
        # Exact branching certificate: can k closed edge neighborhoods
        # cover all edge vertices of L(G)? Branch on an uncovered edge.
        closed=[sum(1<<j for j,f in enumerate(edges) if set(e)&set(f)) for e in edges]
        def can_cover(remaining,k):
            if not remaining:return True
            if not k or remaining.bit_count()>k*volume:return False
            bit=(remaining&-remaining).bit_length()-1
            choices=closed[bit]
            while choices:
                i=(choices&-choices).bit_length()-1
                if can_cover(remaining & ~closed[i],k-1):return True
                choices&=choices-1
            return False
        if can_cover((1<<len(edges))-1,len(selected)-1):
            optimal=gc.min_maximal_matching_number(g)
            assert optimal < len(selected) and gc.domination_number(g)==len(selected)
            print("Implicit refutation:",code,len(g),len(selected),optimal,flush=True)
            counts["implicit"]+=1
        else:counts["branching"]+=1
    assert len(codes)==312 and len(backup)==4700 and len(codes|backup)==4776
    assert counts["eligible"]==327 and counts["refuted_eligible"]==69
    assert counts == {"eligible":327,"refuted_eligible":69,"degree_or_volume":303,"branching":24}
    print("Physical row 574, ID 07b76d4b, 163 touches, proposed with null proof.")
    print("4776 released encodings;",dict(counts),flush=True)

def make_graph(k,compact=False):
    g=nx.Graph()
    for i in range(k):
        g.add_edge(2*i,2*i+1)
    def subdivider(a,b):
        w=len(g)
        g.add_edges_from([(a,w),(b,w)])
    for i in range(k):
        subdivider(2*i,2*((i+1)%k)+1)
    for a in range(2*k):
        for b in range(2*k):
            if a//2==b//2 or (compact and a>=b):
                continue
            for _ in range(1 if compact else 2*k):
                subdivider(a,b)
    return g

def direct(k,compact):
    g=make_graph(k,compact)
    assert gc.nontrivial(g) and gc.eulerian(g) and gc.triangle_free(g)
    gamma=gc.domination_number(g)
    edges=gc.min_maximal_matching_number(g)
    assert (gamma,edges)==(2*k-1,k)
    print(f"k={k}, compact={compact}, order={len(g)}, size={g.number_of_edges()}, GraphCalc values {gamma} and {edges}.",flush=True)

if __name__=="__main__":
    assert version("graphcalc")=="2.0.0" and version("networkx")=="3.5"
    audit(Path(sys.argv[1]).resolve())
    direct(2,True)
    direct(2,False)
    direct(3,False)
