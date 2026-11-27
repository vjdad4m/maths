import itertools,collections
C=7
def edge(g,i,j):g[i].add(j);g[j].add(i)
def inducedP9(g):
 def walk(xs,u):
  if xs.bit_count()==9:return True
  for v in g[u]:
   if not xs>>v&1 and not (bits[v] & (xs ^ (1<<u))):
    if walk(xs|(1<<v),v):return True
  return False
 bits=[sum(1<<v for v in r) for r in g]
 return any(walk(1<<i,i) for i in range(len(g)))
def theta(L):
 n=sum(L)-1;g=[set() for i in range(n)];a=2
 for l in L:
  pp=[0]+list(range(a,a+l-1))+[1];a+=l-1
  for i,j in zip(pp,pp[1:]):edge(g,i,j)
 return g
def dumb(a,b,d):
 n=a+b+d-1
 g=[set() for _ in range(n)]
 for i in range(a):edge(g,i,(i+1)%a)
 start=0 if not d else a+d-1
 P=[start]+list(range(a+d,n))
 assert len(P)==b
 for i in range(b):edge(g,P[i],P[(i+1)%b])
 if d:
  Q=[0]+list(range(a,start+1));assert len(Q)==d+1
  for i,j in zip(Q,Q[1:]):edge(g,i,j)
 return g
def certify(g):
 n=len(g)
 d2=[set.union(*[g[j] for j in g[i]])-{i} for i in range(n)]
 order=[0]
 while len(order)<n:
  done=set(order)
  order.append(max(set(range(n))-done,key=lambda i:(len((g[i]|d2[i])&done),len(g[i]),-i)))
 idx={old:new for new,old in enumerate(order)}
 maskrows=lambda edges:[sum(1<<idx[j] for j in edges[i]) for i in order]
 rows=maskrows(g);two=maskrows(d2)
 def bit(rs,i,j):return (rs[i]>>j)&1
 def near(i,j):return (i-j)%7 in (1,6)
 data=[]
 def adj(nums,i,j):
  if i<7:
   if j<7:return near(i,j)
   return i==nums[j-7]
  if j<7:return j==nums[i-7]
  return bit(rows,i-7,j-7)
 def find(nums):
  m=7+len(nums)
  graph=[{j for j in range(m) if adj(nums,i,j)} for i in range(m)]
  bits=[sum(1<<v for v in r) for r in graph]
  def dfs(path,u,seen):
   if len(path)==9:return path
   for v in sorted(graph[u]):
    if not seen>>v&1 and not(bits[v]&(seen^(1<<u))):
     found=dfs(path+[v],v,seen|(1<<v))
     if found:return found
  for i in range(m):
   found=dfs([i],i,1<<i)
   if found:return 1024+sum(v << (5*k) for k,v in enumerate(found))
 def vertex(seq):
  if len(seq)==n:raise Exception('unexcluded full legal coloring')
  q=len(data)
  row=[0]*7
  data.append(row)
  for c in range(7):
   if any((bit(rows,len(seq),j) and near(c,x)) or
          (bit(two,len(seq),j) and c==x) for j,x in enumerate(seq)):continue
   ss=seq+[c]
   w=find(ss)
   row[c]=w if w else vertex(ss)
  return q
 vertex([0])
 assert len(data)<1024
 return {'n':n,'order':order,'rows':rows,'d2':two,'data':data}
out={}
for L in itertools.combinations_with_replacement(range(1,7),3):
 a,b,c=L
 if a+b>=5 and b+c<=9:out['theta'+str(a)+str(b)+str(c)]=certify(theta(L))
for a,b in itertools.combinations_with_replacement(range(5,7),2):
 for d in range(2):
  if a+b+d<=11:out['dumb'+str(a)+str(b)+str(d)]=certify(dumb(a,b,d))
import json, sys
from pathlib import Path
TEMPLATE = "import BicycleCheck133\n\nnamespace Graffiti133Bicycle.SHAPENAME\ndef outerOrder : Nat := 91001\ndef labeling : List Nat := [91002]\ndef rows : List Nat := [91003]\ndef distanceTwo : List Nat := [91004]\ndef certificate : List (List Nat) := [[91005]]\nset_option maxRecDepth 120000 in\nset_option maxHeartbeats 0 in\ntheorem checked : verify rows distanceTwo certificate (outerOrder-1) 0 [0]=true := by decide\n\nset_option maxRecDepth 120000 in\ntheorem distanceTwo_checked : ∀ i j : Fin outerOrder, bit distanceTwo i.val j.val=true →\n    ∃ k : Fin outerOrder, bit rows i.val k.val=true ∧ bit rows j.val k.val=true := by decide\n\ntheorem forces_induced_nine (s : Nat → Nat) (legal : Legal rows distanceTwo outerOrder s)\n    (zero : s 0=0) : PathExists rows outerOrder s :=\n  numbered_site_zero_has_path (by decide) legal zero checked\n\ntheorem graph_forces_induced_nine {V : Type*} {G : SimpleGraph V}\n    (h4 : Graffiti133.FourCycleFree G) {s : Nat → Nat} (zero : s 0=0)\n    (M : Numbered G rows distanceTwo outerOrder s) :\n    ∃ p : Fin 9 → V, Graffiti133.InducedPath G p :=\n  M.lift (forces_induced_nine s (M.legal h4) zero)\n\n#print axioms graph_forces_induced_nine\nend Graffiti133Bicycle.SHAPENAME\n"
def render(key, d):
    name = ('Theta' + key[5:]) if key.startswith('theta') else ('Dumb' + key[4:])
    lit = lambda obj: json.dumps(obj,separators=(',',':'))
    s = TEMPLATE.replace('SHAPENAME',name).replace('91001',str(d['n']))
    for marker,k in [('[91002]','order'),('[91003]','rows'),('[91004]','d2'),('[[91005]]','data')]:
        s=s.replace(marker,lit(d[k]))
    if key in ("theta444", "theta445"):
        s = s.replace('set_option maxRecDepth 120000 in\nset_option maxHeartbeats 0 in\ntheorem checked : verify rows distanceTwo certificate (outerOrder-1) 0 [0]=true := by decide', 'def firstCheck (c : Nat) : Bool :=\n  if stepLegal rows distanceTwo [0] c then\n    let w := (certificate.getD 0 []).getD c 0\n    if w<1024 then verify rows distanceTwo certificate (outerOrder-2) w [0,c]\n    else pathCheck rows [0,c] (w-1024)\n  else true\n\nset_option maxRecDepth 120000 in\nset_option maxHeartbeats 0 in\nprivate theorem first0 : firstCheck 0=true := by decide\n\nset_option maxRecDepth 120000 in\nset_option maxHeartbeats 0 in\nprivate theorem first1 : firstCheck 1=true := by decide\n\nset_option maxRecDepth 120000 in\nset_option maxHeartbeats 0 in\nprivate theorem first2 : firstCheck 2=true := by decide\n\nset_option maxRecDepth 120000 in\nset_option maxHeartbeats 0 in\nprivate theorem first3 : firstCheck 3=true := by decide\n\nset_option maxRecDepth 120000 in\nset_option maxHeartbeats 0 in\nprivate theorem first4 : firstCheck 4=true := by decide\n\nset_option maxRecDepth 120000 in\nset_option maxHeartbeats 0 in\nprivate theorem first5 : firstCheck 5=true := by decide\n\nset_option maxRecDepth 120000 in\nset_option maxHeartbeats 0 in\nprivate theorem first6 : firstCheck 6=true := by decide\n\ntheorem checked : verify rows distanceTwo certificate (outerOrder-1) 0 [0]=true := by\n  change (List.range 7).all firstCheck=true\n  apply List.all_eq_true.mpr\n  intro i hi\n  have lt := List.mem_range.mp hi\n  rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 by omega) with rfl|rfl|rfl|rfl|rfl|rfl|rfl\n  · exact first0\n  · exact first1\n  · exact first2\n  · exact first3\n  · exact first4\n  · exact first5\n  · exact first6')
    return s
if len(sys.argv) == 1:
    print(json.dumps({k:[d['n'],len(d['data'])] for k,d in out.items()}))
elif sys.argv[1] in out:
    print(render(sys.argv[1],out[sys.argv[1]]),end='')
else:
    dst=Path(sys.argv[1])
    dst.mkdir(parents=True,exist_ok=True)
    for k,d in out.items():
        name=('Theta'+k[5:]) if k.startswith('theta') else ('Dumb'+k[4:])
        (dst/('Bicycle'+name+'133.lean')).write_text(render(k,d),encoding='utf-8')
