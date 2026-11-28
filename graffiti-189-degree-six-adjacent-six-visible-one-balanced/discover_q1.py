"""Discover path masks, not a proof. Run: python discover_q1.py OUTPUT_DIRECTORY."""
from itertools import combinations
from pathlib import Path
import json, sys
import numpy as np

edges0 = list(combinations(range(6), 2))
edgesz = [(i, 9) for i in range(6)]
cases = [(2, 2, 3, 3), (1, 2, 2, 4), (1, 2, 3, 3)]
masks = np.arange(1 << 21, dtype=np.uint32)
P, Z = masks & 32767, masks >> 15
pop = np.array([i.bit_count() for i in range(64)])
degree = np.zeros((1 << 15, 6), dtype=np.int8)
for k, (i, j) in enumerate(edges0):
    bit = ((np.arange(1 << 15) >> k) & 1).astype(np.int8)
    degree[:, i] += bit
    degree[:, j] += bit
output = Path(sys.argv[1])
output.mkdir(parents=True, exist_ok=True)

def discover(mode, idx):
    x, y, a, b = cases[idx]
    fixed = [(6,7), (6,8), (7,8)] + [(i,6) for i in range(x)]
    fixed += [(i,7) for i in range(x,x+y)] + [(i,j) for i in range(x+y,6) for j in (6,7)]
    thresholds = [5-a]*x + [5-b]*y + [4]*(6-x-y)
    good = np.ones(1 << 21, dtype=bool)
    if mode == 'sparse':
        for i,k in enumerate(thresholds):
            good &= degree[P,i] + ((Z>>i)&1) >= k
        good &= pop[Z] >= 3
        edges, n, roots = edges0+edgesz, 10, [9]
    else:
        for i,k in enumerate(thresholds):
            good &= degree[P,i] >= k-1
        good &= Z & ((1<<x)-1) != 0
        good &= Z & (((1<<y)-1)<<x) != 0
        for i in range(6):
            k = (5 if i<x+y else 4) - int(mode=='isolated')
            good &= (degree[P,i] >= k) | ((Z>>i)&1!=0)
        edges, n, roots = edges0, 9, list(range(6))
        if mode == 'isolated':
            fixed += edgesz
            n = 10
    if idx == 1 and mode != 'isolated':
        good &= P != 28700
    all_boards = masks[good]
    minimal = np.ones(len(all_boards), dtype=bool)
    for k in range(21):
        bit = 1 << k
        minimal &= ~((all_boards & bit != 0) & good[all_boards ^ bit])
    boards = all_boards[minimal]
    nbr = [[] for _ in range(n)]
    for k,(i,j) in enumerate(edges):
        nbr[i].append((j,1<<k)); nbr[j].append((i,1<<k))
    for i,j in fixed:
        nbr[i].append((j,0)); nbr[j].append((i,0))
    paths = {}
    def visit(i, unused, mask, path):
        if not unused:
            paths.setdefault(mask,path)
            return
        for j,m in nbr[i]:
            bit = 1<<j
            if unused & bit:
                visit(j,unused^bit,mask|m,path+(j,))
    for r in roots:
        visit(r,((1<<n)-1)^(1<<r),0 if mode=='sparse' else 1<<(15+r),(r,))
    cover = {}
    for m in paths:
        hits = boards & m == m
        if hits.any():
            cover[m] = int.from_bytes(np.packbits(hits,bitorder='little'),'little')
    todo = (1<<len(boards))-1
    templates = []
    while todo:
        m = max(cover,key=lambda m:(cover[m]&todo).bit_count())
        hits = cover.pop(m) & todo
        if not hits:
            raise AssertionError((mode,idx,'uncovered relaxed boards'))
        todo ^= hits
        templates.append((m,paths[m]))
    print(mode,idx,len(all_boards),len(boards),len(templates),flush=True)
    (output / f'{mode}{idx}.json').write_text(json.dumps(templates)+'\n')

for mode in ('sparse','dense','isolated'):
    for idx in range(3):
        discover(mode,idx)
