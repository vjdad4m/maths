"""Certify every eligible released witness against the pinned row."""
from pathlib import Path
from itertools import combinations
from tempfile import TemporaryDirectory
import json
import os
import subprocess
import sys

import networkx as nx


def rainbow_cnf(g, amount):
    n=len(g)
    mark=lambda v: 1+v
    color=lambda v,c: 1+n*(1+c)+v
    clauses=[]
    for v in g:
        choices=[color(v,c) for c in range(3)]
        clauses.append([-mark(v)]+choices)
        for a,b in combinations(choices,2):
            clauses.append([-a,-b])
        for c in range(3):
            clauses.extend([[-color(v,c),mark(v)], [mark(v)]+[color(u,c) for u in g[v]]])
    # Unary prefix-count flags. A real prefix count gives the converse extension.
    flag=lambda i,j: 4*n+(i-1)*(amount+1)+j
    for i in range(1,n+1):
        clauses.append([-mark(i-1),flag(i,1)])
        for j in range(1,min(i,amount+2)):
            clauses.append([-flag(i-1,j),flag(i,j)])
            if j<=amount:
                clauses.append([-mark(i-1),-flag(i-1,j),flag(i,j+1)])
    clauses.append([-flag(n,amount+1)])
    # The first appearance of a color can respect increasing color order.
    for v in g:
        for c in (1,2):
            clauses.append([-color(v,c)]+[color(u,c-1) for u in range(v)])
    return clauses,flag(n,amount+1)


def check_trace(original,path):
    clauses=dict(enumerate(original,1))
    empty=False
    last=len(original)
    for line in path.open():
        words=line.split()
        if words[1]=='d':
            for ref in words[2:-1]: clauses.pop(int(ref),None)
            continue
        row=list(map(int,words)); idx=row[0]
        assert idx>last and row[-1]==0
        last=idx; sep=row.index(0,1); clause=row[1:sep]
        true={-x for x in clause}
        conflict=any(-x in true for x in true)
        for ref in row[sep+1:-1]:
            assert ref>0 and not conflict
            reason=clauses[ref]
            assert not any(x in true for x in reason)
            undecided={x for x in reason if -x not in true}
            assert len(undecided)<=1
            if undecided: true.update(undecided)
            else: conflict=True
        assert conflict
        clauses[idx]=clause; empty |= not clause
    assert empty


def main(checkout):
    p=checkout/'results'
    graphs={r['witness_g6'] for f in p.glob('*refuted.json') for r in json.loads(f.read_text()) if r.get('witness_g6')}
    simple=sat=0
    for code in sorted(graphs):
        g=nx.from_graph6_bytes(code.encode())
        if len(g)<2 or not nx.check_planarity(g)[0] or any(len(c)>=4 for c in nx.find_cliques(g)):
            continue
        h=nx.complement(g)
        colors=min((nx.greedy_color(h,strategy=st) for st in ['largest_first','saturation_largest_first']),
                   key=lambda f:len(set(f.values())))
        assert all(colors[u]!=colors[v] for u,v in h.edges)
        upper=len(set(colors.values()))
        forced={v for v,d in g.degree if d<3}
        optional=sorted((g.degree[v] for v in g if v not in forced),reverse=True)
        lower=next(i for i in range(len(forced),len(g)+1) if 3*(len(g)-i)<=sum(g.degree[v] for v in forced)+sum(optional[:i-len(forced)]))
        if upper<=max(lower,min(len(g),3)):
            simple+=1
            continue
        with TemporaryDirectory() as tmp:
            cnf=Path(tmp)/'rainbow.cnf'; trace=Path(tmp)/'rainbow.lrat'
            clauses,num=rainbow_cnf(g,upper-1)
            cnf.write_text(f'p cnf {num} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
            r=subprocess.run([os.environ.get('CADICAL','cadical'),'-q','-t','60','--lrat','--no-binary',cnf,trace],capture_output=True,text=True)
            if r.returncode==20:
                check_trace(clauses,trace);sat+=1
            else:
                raise AssertionError((len(g), upper, lower, r.returncode, code))
    assert (len(graphs),simple,sat)==(312,137,11)
    print('Released graphs',len(graphs),'elementary certificates',simple,'checked SAT lower bounds',sat,flush=True)

if __name__=='__main__':
    main(Path(sys.argv[1]).resolve())
