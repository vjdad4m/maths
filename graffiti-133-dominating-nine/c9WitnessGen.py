import itertools
N = 9
def candidate(m):
 return tuple(i for i in range(N) if m >> i & 1)
def graph(masks, e=False):
 out=[set() for _ in range(N+len(masks))]
 def add(a,b):out[a].add(b);out[b].add(a)
 for i in range(N):add(i,(i+1)%N)
 for i,m in enumerate(masks):
  for j in candidate(m):add(N+i,j)
 if e:add(9,10)
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
assert len(masks)==57
lit=lambda rs:'['+', '.join(map(str,rs))+']'
print('def singleW : List Nat :=',lit(get(graph([i])) for i in range(512)))
print('def doubleW (e : Bool) : List (List Nat) := if e then')
for e in [True,False]:
 if not e:print('else')
 print(lit(lit(get(graph([a,b],e)) if i!=j else 0 for j,b in enumerate(masks)) for i,a in enumerate(masks)))
