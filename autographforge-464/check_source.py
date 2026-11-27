"""Source checks and direct GraphCalc verification for normalized row 464."""
import json
import subprocess
import sys
from pathlib import Path
from importlib.metadata import version

import networkx as nx
import graphcalc.graphs as gc
from corpus import main as check_corpus

PIN = '4d1a8afc99447cacd2328cca20e47b6493e8dbc5'
ID = 'f488855f'
CLAIM = '(((nontrivial) ∧ (K_4_free)) ∧ (planar)) ⇒ vertex_clique_cover_number ≤ three_rainbow_domination_number'


def release(checkout):
    head = subprocess.check_output(['git','-C',checkout,'rev-parse','HEAD'],text=True).strip()
    assert head == PIN
    p = checkout / 'results'
    lines = (p/'survivors_by_touch_normalised.txt').read_text().splitlines()
    assert lines[463] == f'[   220] {CLAIM}    -- promising:class'
    assert sum(CLAIM in line for line in lines) == 1
    record, = (r for r in json.loads((p/'cegis_results.json').read_text())['conjectures'] if r['id']==ID)
    assert record['status']=='proposed' and record['lean_proof'] is None and record['statement']==CLAIM
    for f in (p/'verified_proofs').glob('*.lean'):
        assert ID not in f.read_text() and CLAIM not in f.read_text()
    for path in p.glob('*refuted.json'):
        for r in json.loads(path.read_text()):
            assert r.get('id')!=ID and r.get('statement')!=CLAIM
    print(f'Physical row 464 = {ID}, 220 touches, proposed, null Lean proof.')


def direct(m):
    g=nx.Graph()
    for i in range(m):
        for y in [2+3*i,4+3*i]:
            g.add_edges_from([(0,y),(1,y),(3+3*i,y)])
    assert len(g)==3*m+2 and g.number_of_edges()==6*m
    assert gc.nontrivial(g) and gc.planar(g) and gc.K_4_free(g) and gc.connected(g) and nx.is_bipartite(g)
    cover=gc.vertex_clique_cover_number(g)
    rainbow=gc.three_rainbow_domination_number(g)
    assert (cover,rainbow)==(2*m,m+2)
    print(f'm={m}, order={len(g)}, connected, bipartite, planar, K4-free, clique cover={cover}, singleton rainbow={rainbow}.')


if __name__=='__main__':
    assert version('graphcalc')=='2.0.0' and version('networkx')=='3.5'
    checkout=Path(sys.argv[1]).resolve()
    release(checkout)
    check_corpus(checkout)
    for m in [2,3,4]:
        direct(m)
