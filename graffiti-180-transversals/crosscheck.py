"""Compare the C++ summary for every small connected graph against direct enumeration."""
from itertools import combinations
from pathlib import Path
import subprocess
import sys

folder = Path(__file__).resolve().parent

def subsets(vertices):
    for k in range(len(vertices) + 1):
        for xs in combinations(vertices, k):
            yield frozenset(xs)

def read_graph(line):
    n = ord(line[0]) - 63
    adj = [set() for _ in range(n)]
    pairs = [(i, j) for j in range(n) for i in range(j)]
    for k, (i, j) in enumerate(pairs):
        val = ord(line[1 + k // 6]) - 63
        if val >> (5 - k % 6) & 1:
            adj[i].add(j)
            adj[j].add(i)
    return adj

def distance(adj, root):
    dist = {root: 0}
    todo = [root]
    for x in todo:
        for y in adj[x]:
            if y not in dist:
                dist[y] = dist[x] + 1
                todo.append(y)
    return dist

def bipartite(adj, subset):
    color = {}
    for root in subset:
        if root in color:
            continue
        color[root] = 0
        todo = [root]
        for x in todo:
            for y in subset & adj[x]:
                if y not in color:
                    color[y] = 1 - color[x]
                    todo.append(y)
                elif color[x] == color[y]:
                    return False
    return True

def leaf_sets(adj):
    edges = [(i,j) for i,nbs in enumerate(adj) for j in nbs if i<j]
    leaves = set()
    for chosen in combinations(edges, len(adj) - 1):
        tree = [set() for _ in adj]
        for i, j in chosen:
            tree[i].add(j)
            tree[j].add(i)
        if len(distance(tree, 0)) == len(adj):
            leaves.add(frozenset(i for i, nbs in enumerate(tree) if len(nbs) == 1))
    return leaves

def direct(line):
    adj = read_graph(line)
    n = len(adj)
    V = frozenset(range(n))
    subs = list(subsets(sorted(V)))
    out = dict(inputs=1, connected_nonbipartite_prime=0, qualifying_roots=0,
               first_tests=0, second_tests=0, second_needing_credit=0, second_without_global_maximum=0)
    if len(distance(adj, 0)) < n or bipartite(adj, V):
        return out
    for M in subs:
        if 1 < len(M) < n and all(not (adj[i] & M) or M <= adj[i] for i in V - M):
            return out
    out['connected_nonbipartite_prime'] = 1
    trees = leaf_sets(adj)
    bip = [S for S in subs if bipartite(adj, S)]
    b = max(map(len, bip))
    independent = [A for A in subs if all(not (adj[i] & A) for i in A)]
    for r in V:
        if any(adj[r] | adj[s] == V for s in adj[r]):
            continue
        out['qualifying_roots'] += 1
        dist = distance(adj, r)
        for p in (0, 1):
            P = {i for i in V if dist[i] % 2 == p}
            for A in independent:
                D = A & P
                U = A | P
                if r not in D:
                    U = U - {r}
                leaves = max(len(U & T) for T in trees)
                order = max(len(Z) for Z in bip if D <= Z)
                need = 1 + len(A) + len(P) - leaves
                assert order >= need, (line, r, p, A)
                out['first_tests'] += 1
                if p == 1 and r in A:
                    pinned = [Z for Z in bip if D | {r} <= Z]
                    plain = max(map(len, pinned))
                    credited = max(len(Z) + int(not (Z & adj[r])) for Z in pinned)
                    assert credited >= need, (line, r, p, A)
                    out['second_tests'] += 1
                    out['second_needing_credit'] += int(plain < need)
                    out['second_without_global_maximum'] += int(plain < b)
    return out

def check(geng, n):
    lines = subprocess.check_output([geng, '-cq', str(n)], text=True).splitlines()
    for line in lines:
        expected = direct(line)
        actual = subprocess.check_output([folder / '.build/search'], input=line + '\n', text=True)
        fields = actual.splitlines()[0].split()
        summary = {k: int(v) for k, v in zip(fields[::2], fields[1::2])}
        assert expected == summary, (line, expected, summary)
    print(f'Order {n}: matched all seven counters separately on {len(lines)} connected graphs.', flush=True)

if __name__ == '__main__':
    for order in (3, 4, 5, 6, 7):
        check(sys.argv[1], order)
