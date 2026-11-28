from collections import deque
for d in range(7, 15):
    sizes = [2, d-1, d-2, d, 1]
    layer = [i for i,m in enumerate(sizes) for _ in range(m)]
    G = [{j for j,b in enumerate(layer) if i!=j and abs(a-b)<=1}
         for i,a in enumerate(layer)]
    D = []
    for i in range(len(G)):
        q,dist=deque([i]),{i:0}
        while q:
            v=q.popleft()
            for u in G[v]-dist.keys():
                dist[u]=dist[v]+1
                q.append(u)
        D.append(dist)
    x,w = 0,len(layer)-1
    assert sorted(map(len,G))[1]>=d
    # The only cuts must empty an internal layer to make a gap; emptying
    # the d−2 central layer is enough, and fewer than d−2 cannot do so.
    assert min(sizes[1:-1]) == d-2
    assert max(sum(v%2==0 for v in u.values()) for u in D)<=d+1
    assert D[x][w]==4 and sum(v==4 for v in D[x].values())==1
    assert sum(v==4 for v in D[w].values())==2
    assert all(D[w][y]==3 for y in G[x] if y!=1)
    assert D[w][1]==4
    assert all(v+1 in G[v] for v in range(w))
print('d=7..14: checked tight fourth-shell reciprocity, cap, degrees and minimum separating interior layer; each traceable.')
