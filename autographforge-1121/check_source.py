"""Audit row 1121, certify all eligible released witnesses, and check GraphCalc."""
import json
import subprocess
import sys
from importlib.metadata import version
from pathlib import Path

import graphcalc.graphs as gc
import networkx as nx

PIN = '4d1a8afc99447cacd2328cca20e47b6493e8dbc5'
ID = '6deb0d7d'
STATEMENT = '((nontrivial) ∧ (subcubic)) ⇒ vertex_clique_cover_number ≤ three_rainbow_domination_number'


def check_release(checkout):
    head = subprocess.check_output(['git', '-C', checkout, 'rev-parse', 'HEAD'], text=True).strip()
    assert head == PIN
    results = checkout / 'results'
    lines = (results / 'survivors_by_touch_normalised.txt').read_text().splitlines()
    assert lines[1120] == f'[    62] {STATEMENT}    -- promising:class'
    assert sum(STATEMENT in line for line in lines) == 1
    conjectures = json.loads((results / 'cegis_results.json').read_text())['conjectures']
    record, = (r for r in conjectures if r['id'] == ID)
    assert record['statement'] == STATEMENT
    assert record['status'] == 'proposed' and record['lean_proof'] is None
    for path in (results / 'verified_proofs').glob('*.lean'):
        source = path.read_text()
        assert ID not in source and STATEMENT not in source
    witnesses = set()
    for name in ['cegis_refuted', 'conjecturing_refuted', 'property_conjecturing_refuted']:
        for record in json.loads((results / (name + '.json')).read_text()):
            assert record.get('id') != ID and record.get('statement') != STATEMENT
            if record.get('witness_g6'):
                witnesses.add(record['witness_g6'])
    print(f'Physical row 1121 = {ID}, 62 touches, proposed, null Lean proof.')
    return witnesses


def edge_pairs(g):
    pairs = nx.max_weight_matching(g, maxcardinality=True)
    assert nx.is_matching(g, pairs)
    return len(pairs)


def check_corpus(witnesses):
    eligible = 0
    for code in sorted(witnesses):
        g = nx.from_graph6_bytes(code.encode())
        if not (gc.nontrivial(g) and gc.subcubic(g)):
            continue
        eligible += 1
        # Matched pairs and singletons are a clique partition of the whole graph.
        clique_upper = len(g) - edge_pairs(g)
        # Every uncolored vertex has degree 3 and three colored neighbors.
        # Thus the uncolored vertices are independent in the degree-3 subgraph,
        # with at most one vertex in each pair or singleton of its partition.
        core = g.subgraph([v for v, degree in g.degree if degree == 3])
        zeros_upper = len(core) - edge_pairs(core)
        assert clique_upper <= len(g) - zeros_upper, code
    assert (len(witnesses), eligible) == (312, 125)
    print(f'All {eligible} eligible graphs among {len(witnesses)} released graph6 witnesses pass.')


def check_optimizers():
    assert version('graphcalc') == '2.0.0' and version('networkx') == '3.5'
    for m in [3, 4, 7]:
        g = nx.complete_bipartite_graph(3, m)
        assert gc.nontrivial(g) and gc.subcubic(g) == (m == 3)
        assert gc.vertex_clique_cover_number(g) == m
        assert gc.three_rainbow_domination_number(g) == 3
    isolated = nx.disjoint_union(nx.complete_bipartite_graph(3, 3), nx.empty_graph(1))
    assert gc.nontrivial(isolated) and gc.subcubic(isolated)
    assert gc.vertex_clique_cover_number(isolated) == gc.three_rainbow_domination_number(isolated) == 4
    print('GraphCalc 2.0.0: K(3,3), K(3,4), K(3,7), and K(3,3) plus an isolate pass.')


if __name__ == '__main__':
    check_corpus(check_release(Path(sys.argv[1]).resolve()))
    check_optimizers()
