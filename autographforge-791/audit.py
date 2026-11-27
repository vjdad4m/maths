"""Validate pinned row spellings, released cubic inputs and the numerical witness."""
from collections import Counter
from importlib.metadata import version
from pathlib import Path
import itertools
import json
import random
import subprocess
import sys

import graphcalc.graphs as gc
import networkx as nx

PIN = "4d1a8afc99447cacd2328cca20e47b6493e8dbc5"
ROWS = {
    791: ("5550b3d6", "((nontrivial) ∧ (cubic)) ⇒ three_rainbow_domination_number ≤ (2 · min_maximal_matching_number)", 630),
    2732: ("81cb4a70", "((nontrivial) ∧ (cubic)) ⇒ ((1/2) · three_rainbow_domination_number) ≤ min_maximal_matching_number", 584),
    3754: ("27dd6555", "((2 · min_maximal_matching_number) < three_rainbow_domination_number) ⇒ ¬cubic", 0),
    5177: ("8fc5440b", "(min_maximal_matching_number < ((1/2) · three_rainbow_domination_number)) ⇒ ¬cubic", 0),
}

def release(checkout):
    def git(*args):
        return subprocess.check_output(["git","-C",checkout,*args],text=True)
    assert git("rev-parse","HEAD").strip() == PIN
    root = checkout/"results"
    lines = (root/"survivors_by_touch_normalised.txt").read_text().splitlines()
    recs = json.loads((root/"cegis_results.json").read_text())["conjectures"]
    for row,(key,claim,touches) in ROWS.items():
        expected = "[    97] " if row in (791,2732) else "[     -] "
        assert lines[row-1] == expected + claim + ("    -- promising:class" if row == 791 else "")
        rec, = [r for r in recs if r["id"] == key]
        assert rec["status"]=="proposed" and rec["statement"]==claim
        assert rec["lean_statement"] is None and rec["lean_proof"] is None and rec["metadata"]["touches"]==touches
        for p in (root/"verified_proofs").glob("*.lean"):
            assert key not in p.read_text() and claim not in p.read_text()
        print(f"{row} {key}: proposed; source-record touches {touches}; no Lean statement or proof.")
    assert lines[2732].strip() == "== "+ROWS[791][1]
    assert all(not w for rec in recs for w in rec.get("tightness_witnesses",[]))
    refs=set()
    files=list(root.glob("*refuted.json"))
    assert len(files)==3
    for p in files:
        for rec in json.loads(p.read_text()):
            assert all(rec.get("id")!=key and rec.get("statement")!=claim for key,claim,_ in ROWS.values())
            if rec.get("witness_g6"): refs.add(rec["witness_g6"])
    backups=[l for l in git("ls-tree","-r","HEAD","--","results").splitlines() if l.endswith("/graphs.g6")]
    blob = "088f28b308df1405d6b63cfd44ec3931c1a9556e"
    assert len(backups)==4 and {l.split()[2] for l in backups}=={blob}
    codes=set(git("cat-file","blob",blob).splitlines())
    assert (len(codes),len(refs),len(codes|refs))==(4700,312,4776)
    return codes | refs,refs


def witness():
    pairs=[(0,1),(0,2),(1,2),(1,2),(3,4),(3,5),(4,6),(4,7),(5,6),(5,7),(0,3),(6,7)]
    g=nx.Graph()
    g.add_nodes_from(range(20))
    for i,(u,v) in enumerate(pairs):
        g.add_edges_from([(8+i,u),(8+i,v)])
        if i%2: g.add_edge(8+i-1,8+i)
    return g


def valid(g, labels):
    return all(c in range(4) for c in labels) and all(
        labels[v] or {labels[w] for w in g[v]} == {1,2,3} for v in g)


def find_labeling(g, budget, rng, attempts):
    """Every returned labeling is checked. An unsuccessful trial establishes no lower bound."""
    count=len(g)-budget
    if count<=0: return [1]*len(g)
    N=[set(g[v]) for v in range(len(g))]
    def extend(Z):
        clash=[set() for _ in g]
        for v in Z:
            for a,b in itertools.combinations(N[v],2):
                clash[a].add(b); clash[b].add(a)
        labels=[0 if v in Z else 1 for v in g]
        todo={v for v in g if clash[v]}
        for v in todo: labels[v]=0
        def paint(left):
            if not left: return True
            def blocked(v): return {labels[w] for w in clash[v] if labels[w]}
            v=max(left,key=lambda u:(len(blocked(u)),len(clash[u]),u))
            for c in sorted({1,2,3}-blocked(v)):
                labels[v]=c
                if paint(left-{v}):return True
            labels[v]=0
            return False
        if paint(todo):
            assert valid(g,labels) and sum(bool(c) for c in labels)<=budget
            return labels
    for _ in range(attempts):
        remain=set(g); zeros=[]
        while remain and len(zeros)<count:
            v=min(sorted(remain),key=lambda u:len(N[u]&remain)+rng.random()*2.5)
            zeros.append(v)
            remain-=N[v]|{v}
        if len(zeros)==count:
            colors=extend(set(zeros))
            if colors is not None:return colors
    return None


def corpus(codes,refs):
    stats=Counter()
    failures=[]
    for code in sorted(codes):
        g=nx.from_graph6_bytes(code.encode())
        if len(g)<2 or not gc.cubic(g): continue
        stats["eligible"]+=1
        stats["from_refutations"]+=code in refs
        # One selected edge dominates at most five edges in a cubic graph.
        lo=sum((g.subgraph(c).number_of_edges()+4)//5 for c in nx.connected_components(g))
        rng=random.Random(code)
        if find_labeling(g,2*lo,rng,100) is not None:
            stats["labeling_and_count"]+=1
            continue
        lo=gc.min_maximal_matching_number(g)
        if find_labeling(g,2*lo,rng,250) is not None:
            stats["labeling_and_exact_matching"]+=1
            continue
        rainbow=gc.three_rainbow_domination_number(g)
        stats["both_optimizers"]+=1
        if rainbow>2*lo:failures.append((len(g),rainbow,lo,code))
    print("4776 released graph6 encodings; cubic numeric checks:",dict(stats))
    print("Violations in released encodings:",failures)


def battery(checkout):
    sys.path.insert(0,str(checkout))
    from pipeline.invariants_graphcalc import compute_battery
    g=witness()
    labels=[1,0,0,3,0,0,0,0,2,2,1,3,2,2,1,3,3,1,0,2]
    assert valid(g,labels) and sum(bool(c) for c in labels)==13
    frame=compute_battery([g],workers=1,cap_s=3,max_n=9)
    names=["order","nontrivial","connected","cubic","three_rainbow_domination_number","min_maximal_matching_number"]
    print("Public compute_battery witness row:",dict(frame.loc[0,names]))
    assert tuple(frame.loc[0,names])==(20,True,True,True,13,6)
    print("Witness graph6:",nx.to_graph6_bytes(g,header=False).decode().strip())


if __name__=="__main__":
    assert version("graphcalc")=="2.0.0" and version("networkx")=="3.5"
    checkout=Path(sys.argv[1]).resolve()
    corpus(*release(checkout))
    battery(checkout)
