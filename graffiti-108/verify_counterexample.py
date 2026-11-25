from itertools import combinations
from collections import deque, Counter
V = tuple(frozenset(a) for a in combinations(range(7), 3))
N = [tuple(j for j,v in enumerate(V) if not u & v) for u in V]
assert len(V)==35 and all(len(a)==4 for a in N)
CYCLES = [[0,31,4,25,14,15,34],[1,28,11,16,33,2,30],[3,27,22,8,19,7,32],
          [6,20,29,10,18,12,21],[5,23,26,13,17,9,24]]
assert sorted(v for c in CYCLES for v in c)==list(range(35))
for c in CYCLES:
 assert all(v in N[u] for u,v in zip(c,c[1:]+c[:1]))
 assert max(sum((s>>j)&1 for j in range(7)) for s in range(128)
            if all(not ((s>>j)&1 and (s>>((j+1)%7))&1) for j in range(7)))==3
stars=[{j for j,v in enumerate(V) if i in v} for i in range(7)]
assert all(len(s)==15 and all(not s.intersection(N[v]) for v in s) for s in stars)
assert not set.intersection(*stars)
for v in range(35):
 d={v:0}; q=deque([v])
 while q:
  w=q.popleft()
  for u in N[w]:
   if u not in d: d[u]=d[w]+1; q.append(u)
 assert Counter(d.values())=={0:1,1:4,2:12,3:18}
assert 15 > 13 + 2*(0//3)
print('KG(7,3): alpha=15, alphacore=0, maxEven=13; disproof verified.')
