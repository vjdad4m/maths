"""Independent enumeration of the eight-vertex fixture using only the standard library."""
from itertools import combinations

vertices = frozenset(range(8))
edges = [(0,3),(0,4),(0,6),(0,7),(1,4),(1,5),(1,7),(2,5),(2,6),(3,7),(4,6),(5,7)]
def adjacency(E):
    result = [set() for _ in vertices]
    for x, y in E:
        result[x].add(y)
        result[y].add(x)
    return result
adj = adjacency(edges)

def dist(g, r):
    d = {r: 0}
    pending = [r]
    for x in pending:
        for y in g[x]:
            if y not in d:
                d[y] = 1+d[x]
                pending.append(y)
    return d

def proper(g, S, colors):
    return all(colors[x] != colors[y] for x in S for y in g[x] & S)
def colorings(S):
    S = tuple(sorted(S))
    for mask in range(1 << len(S)):
        colors = {v:(mask >> i) & 1 for i,v in enumerate(S)}
        if proper(adj, set(S), colors):
            yield colors
def subsets():
    return (frozenset(s) for k in range(9) for s in combinations(range(8), k))

assert all(any(adj[x] & M and not M <= adj[x] for x in vertices-M) for M in subsets() if 1 < len(M) < 8)
assert all(adj[2] | adj[y] != vertices for y in adj[2])
distance = dist(adj, 2)
P = frozenset(x for x in vertices if distance[x] % 2 == 0)
A = frozenset([0,1,2])
assert not any(adj[x] & A for x in A)
assert A <= P
W = 0
trees = 0
for E in combinations(edges,7):
    tree = adjacency(E)
    if len(dist(tree,2)) == 8:
        trees += 1
        W = max(W,sum(len(tree[v]) == 1 for v in P))
B = 8+W-(1+len(A)+len(P))
assert (W,B)==(3,2)
bip = [s for s in subsets() if next(colorings(s),None) is not None]
assert max(map(len,bip))==6
pairs = sorted(tuple(sorted(vertices-s)) for s in bip if len(s)==6)
assert pairs==[(0,1),(0,5),(4,7),(6,7)]
old = list(colorings(vertices-{0,5}))
solutions = [s for s in bip if len(s)>=8-B and A<=s]
assert all(c[1]!=c[2] for c in old)
assert all(5 in s and all(e[1]==e[2] for e in colorings(s)) for s in solutions)
print('Graph GCpdUg, prime, root 2, no incident dominating edge.')
print('Spanning trees checked:', trees)
print('Eligible optimum, allowance, bipartite order:', W,B,6)
print('Minimum transversals:', pairs)
print('Allowed deletions for the marking:', sorted(tuple(sorted(vertices-s)) for s in solutions))
print('Previous colors of 1 and 2 are opposite; after every successful repair they coincide.')
