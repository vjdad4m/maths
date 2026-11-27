import itertools
N = 7
def candidate(m):
 return tuple(i for i in range(N) if m >> i & 1)
def graph(masks, e=False):
 out=[set() for _ in range(N+len(masks))]
 def add(a,b):out[a].add(b);out[b].add(a)
 for i in range(N):add(i,(i+1)%N)
 for i,m in enumerate(masks):
  for j in candidate(m):add(N+i,j)
 if e:add(7,8)
 return out
def pack(t,z):return t+sum(x << (4*(i+1)) for i,x in enumerate(z))
def get(g):
 for i in range(len(g)):
  for j in range(i+1,len(g)):
   common=sorted(g[i]&g[j])
   if len(common)>=2:return pack(1,[i,j,*common[:2]])
 def dfs(p,s):
  if len(p)==N:return p
  for u in sorted(g[p[-1]]-s):
   if not g[u]&(s-{p[-1]}):
    r=dfs(p+[u],s|{u})
    if r:return r
 for i in range(len(g)):
  p=dfs([i],{i})
  if p:return pack(2,p)
 return 0
masks=[]
for z in range(1,6):
 for p in itertools.combinations(range(N),z):
  m=sum(1<<i for i in p)
  if not get(graph([m])):masks.append(m)
assert len(masks)==14
lit=lambda rs:'['+', '.join(map(str,rs))+']'
print('def singleW : List Nat :=',lit(get(graph([i])) for i in range(128)))
print('def doubleW (e : Bool) : List (List Nat) := if e then')
for e in [True,False]:
 if not e:print('else')
 print(lit(lit(get(graph([a,b],e)) if i!=j else 0 for j,b in enumerate(masks)) for i,a in enumerate(masks)))

print('def profiles : List Nat :=',lit(masks))
J=[sum(1<<j for j,b in enumerate(masks) if i!=j and not get(graph([a,b]))) for i,a in enumerate(masks)]
print('def compatRows : List Nat :=',lit(J))
def ok(i,j):return J[i]>>j&1
assert not any(not get(graph([a,b],True)) for i,a in enumerate(masks) for j,b in enumerate(masks) if i!=j)
def color(S):
 col={}
 for _ in S:
  used=lambda i:{col[j] for j in col if ok(i,j)}
  t=max(S-col.keys(),key=lambda i:(len(used(i)),sum(ok(i,j) for j in S),-i))
  col[t]=next(c for c in range(len(S)) if c not in used(t))
 return col
def cert(S,k):
 d=color(S)
 if max(d.values(),default=-1)<k:return '.color '+lit(d.get(i,k) for i in range(14))
 v=max(S,key=lambda i:(d[i],sum(ok(i,j) for j in S),-i))
 return f'.split {v} ({cert(S-{v},k)}) ({cert({j for j in S if j!=v and ok(j,v)},k-1)})'
print('def coreCert : Graffiti133C9.CliqueCert :=',cert(set(range(14)),3))
