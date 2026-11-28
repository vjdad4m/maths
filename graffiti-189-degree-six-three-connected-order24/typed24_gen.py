"""Typed Eq24 CNF/RUP emitter. Solver output is NOT proof until Lean replay."""
import argparse,itertools,json,pathlib,re,subprocess
p=argparse.ArgumentParser()
p.add_argument('--solver',required=True);p.add_argument('--out',required=True)
p.add_argument('--case',default='.*');p.add_argument('--variant',choices=['small','strong'],default='strong')
p.add_argument('--seconds',type=int,default=8);p.add_argument('--retain',action='store_true')
a=p.parse_args()
out=pathlib.Path(a.out);out.mkdir(parents=True,exist_ok=True)
n=24;V=range(n)
def pk(g,i,j,k):return ((g*n+i)*n+j)*n+k+1
def edge(i,j):return pk(0,min(i,j),max(i,j),0)
def near(i,j):return pk(1,min(i,j),max(i,j),0)
def high(i):return pk(3,i,0,0)
def cnt(mode,i,j,k):return pk(5 if mode else 4,i,j,k)
def B(q):return 'true' if q else 'false'
def case(t,b,m):
    name=f'T{t}B{b}M{m}'
    if not re.fullmatch(a.case,name):return
    c=12 if m==0 else 11;g=7-t
    A=range(1,7);BB=range(7,7+b);C=range(7+b,7+b+c)
    S=range(1,1+t);M=range(7,7+t);ly=[0]+[1]*6+[2]*b+[3]*c+[4]*(17-b-c)
    short=t-1 if m==1 else 1
    hole=(short+1)*g-1
    def raw(pos):return pos+int(m!=0 and pos>=hole)
    def in_group(i,j):
        r=raw(j-(7+b))
        return r//g==i or (m==2 and i==1 and r==g-1)
    def first(i,j):
        r=raw(j-(7+b))
        return r//g==i and r%g==0
    def full(i):return m!=1 or i-1!=short
    adj={};d2={}
    for i,j in itertools.combinations(V,2):
        if i==0:q=j in A
        elif ly[i]+1<ly[j]:q=False
        elif i in S and j in A and j not in S and full(i):q=True
        elif i in S and j in M:q=j==i+6
        elif i in M and j in C:q=False if not in_group(i-7,j) else True if first(i-7,j) else None
        else:q=None
        if q is not None:adj[i,j]=q
        if i==0:q=j in BB
        elif i in S and j in C:q=in_group(i-1,j)
        elif i in S and full(i) and not (j in S or (j in M and j!=i+6)):q=False
        else:q=None
        if q is not None:d2[i,j]=q
    rows=[]
    def add(lean,*cl):rows.append((lean,list(cl)))
    def ordinary(rule,*cl):add(f'.ordinary ({rule})',*cl)
    for i in V:
        ordinary(f'.loop {i}',-edge(i,i));ordinary(f'.selfNear {i}',-near(i,i))
    for (i,j),q in adj.items():ordinary(f'.fixedEdge {i} {j} {B(q)}',edge(i,j) if q else -edge(i,j))
    for (i,j),q in d2.items():ordinary(f'.fixedNear {i} {j} {B(q)}',near(i,j) if q else -near(i,j))
    for i,j in itertools.permutations(S,2):
        if full(i):ordinary(f'.cross {i} {j}',-near(i,j+6),edge(i,j))
    def can(i,j):return i!=j and adj.get(tuple(sorted((i,j))),True)
    for i,j in itertools.combinations(V,2):
        ordinary(f'.nearNonedge {i} {j}',-near(i,j),-edge(i,j))
        if adj.get((i,j)) is True or d2.get((i,j)) is True:continue
        for k in V:
            if can(i,k) and can(j,k):
                ordinary(f'.lower {i} {k} {j}',-edge(i,k),-edge(k,j),edge(i,j),near(i,j))
    strong=a.variant=='strong'
    if strong:
        for i in V:
            if i==0:continue
            pp=[j for j in V if ly[j]+1==ly[i]]
            ordinary(f'.parent {i} {pp}',*[edge(i,j) for j in pp])
    highlist=list(V) if strong else list(M)+list(C)
    for i,j in itertools.combinations(highlist,2):
        ordinary(f'.highPair {i} {j}',high(i),high(j))
    caps=list(M)+list(S) if strong else list(M)+([t] if m==1 else [])
    for mode,vertices,limit in ((False,highlist,6),(True,caps,7)):
        met=near if mode else edge
        for i in vertices:
            for j in V:add(f'.zero {B(mode)} {i} {j}',cnt(mode,i,j,0))
            add(f'.base {B(mode)} {i} true',-cnt(mode,i,0,1),met(i,0))
            add(f'.base {B(mode)} {i} false',-met(i,0),cnt(mode,i,0,1))
            for k in range(2,limit+1):add(f'.impossibleBase {B(mode)} {i} {k}',-cnt(mode,i,0,k))
            for j in range(1,n):
                for k in range(1,limit+1):
                    X=cnt(mode,i,j,k);Y=cnt(mode,i,j-1,k);Z=cnt(mode,i,j-1,k-1);W=met(i,j)
                    for u,cl in enumerate(([-Y,X],[-Z,-W,X],[-X,Y,Z],[-X,Y,W])):
                        add(f'.step {B(mode)} {i} {j} {k} {u}',*cl)
            if mode:add(f'.capFinal {i}',-cnt(True,i,23,7))
            else:add(f'.fromHigh {i}',-high(i),cnt(False,i,23,6))
    def cnf(path,rr):
        with path.open('w') as f:
            print('p cnf',6*n**3,len(rr),file=f)
            for _,cl in rr:print(*cl,0,file=f)
    bare=out/(name+'.raw.cnf');trace=out/(name+'.raw.lrat')
    cnf(bare,rows)
    rr=subprocess.run([a.solver,'-q','-t',str(a.seconds),'--lrat','--no-binary',str(bare),str(trace)],
        text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    if 's UNSATISFIABLE' not in rr.stdout:
        print(json.dumps(dict(frame=name,result=rr.stdout[-400:],raw=len(rows))),flush=True)
        return
    R={}
    for l in trace.read_text().splitlines():
        ss=l.split()
        if not ss or ss[1]=='d':continue
        z=ss.index('0',1)
        R[int(ss[0])]=(list(map(int,ss[1:z])),list(map(int,ss[z+1:-1])))
    stack=[[i for i,(cl,_) in R.items() if not cl][-1]]
    used=set();leaf=set();rat=0
    while stack:
        i=stack.pop()
        if i<0:rat+=1
        i=abs(i)
        if i<=len(rows):leaf.add(i);continue
        if i in used:continue
        used.add(i);stack.extend(R[i][1])
    print(json.dumps(dict(frame=name,result='UNSAT',raw=len(rows),slice_initial=len(leaf),slice_additions=len(used),
        rat_hints=rat,bytes=trace.stat().st_size,variant=a.variant)),flush=True)
    if rat==0 and a.retain:
        leaf=sorted(leaf);used=sorted(used)
        ren={old:i+1 for i,old in enumerate(leaf+used)}
        chosen=[rows[i-1] for i in leaf]
        cnf(out/(name+'.cnf'),chosen)
        with (out/(name+'.lrat')).open('w') as f:
            for i in used:
                cl,pf=R[i]
                print(ren[i],*cl,0,*(ren[j] for j in pf),0,file=f)
        body='\n'.join(f'  {r},' for r,_ in chosen)
        lean=f'''import Equality24CountMiddle189
import GraphRup189
open Finset SimpleGraph Graffiti189LongestPath
open Graffiti189LongestPath.Equality24Profile Graffiti189LongestPath.Equality24Count
set_option maxRecDepth 60000
set_option maxHeartbeats 100000000
namespace Graffiti189LongestPath.Equality24Count.{name}
def rules : List Equality24Count.Rule := [
{body}
]
graph_rup certificate (include_str "{name}.cnf") (include_str "{name}.lrat")
theorem impossible {{G : SimpleGraph Vert}} [DecidableRel G.Adj] (M : Model G {m} {t} {b}) : False := by
  have equality : certificate.formula=rules.map Equality24Count.Rule.clause := rfl
  have valid : rules.all (fun r => decide (r.WF {m} {t} {b}))=true := by decide
  have checked := certificate
  rw [equality] at checked
  exact Equality24Count.contradiction_of_proof M rules
    (fun r hr => of_decide_eq_true (List.all_eq_true.mp valid r hr)) checked
#print axioms impossible
end Graffiti189LongestPath.Equality24Count.{name}
'''
        (out/(f'Equality24{name}Cert189.lean')).write_text(lean)
    bare.unlink();trace.unlink()
for b in (4,5,6):
    for t in (3,4):
        for m in ((0,1,2) if b<6 else (1,2)):
            case(t,b,m)
