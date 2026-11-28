from itertools import *
pair = [(0,1),(0,2),(1,2)] + [(i,3+j) for i in range(3) for j in range(3)] + [(3+i,9+j) for i in range(3) for j in range(2)]
fixed=[(6,7),(6,8),(7,8),(6,9),(7,10)]+[(i,j) for i in range(3) for j in (6,7)]
arr = [[] for _ in range(11)]
for k,(i,j) in enumerate(pair):arr[i].append((j,1<<k));arr[j].append((i,1<<k))
for i,j in fixed:arr[i].append((j,0));arr[j].append((i,0))
paths={}
def search(cur,U,mask,path):
  if not U:
    paths.setdefault(mask,path);return
  for j,m in arr[cur]:
    if U>>j&1:search(j,U^(1<<j),mask|m,path+(j,))
for a in range(3,6):search(a,2047^(1<<a),0,(a,))
print('paths',len(paths))
boards=[]
for e in (3,5,6,7):
  C=[0,0,0]
  for k,(i,j) in enumerate(pair[:3]):
    if e>>k&1:C[i]+=1;C[j]+=1
  for M in range(512):
    ch=[(M>>(i*3)&7).bit_count() for i in range(3)]
    if any(i+j<2 for i,j in zip(C,ch)):continue
    wh=[sum(M>>(i*3+j)&1 for i in range(3)) for j in range(3)]
    for B in range(64):
      dv=[wh[j]+(B>>(2*j)&3).bit_count() for j in range(3)]
      if min(dv)<3 or max(dv)<4:continue
      boards.append(e|(M<<3)|(B<<12))
print('boards',len(boards))
from collections import defaultdict
covers={}
lookup={b:i for i,b in enumerate(boards)}
U=(1<<len(boards))-1
for m,p in paths.items():
  l=((1<<18)-1)^m
  k=l; C=0
  while True:
    i=lookup.get(k|m)
    if i is not None:C|=1<<i
    if not k:break
    k=(k-1)&l
  if C:covers[m]=C
sels=[]
while U:
  m=max(covers,key=lambda m:(covers[m]&U).bit_count())
  overlap=covers[m]&U
  if not overlap:
    print('incomplete');break
  U^=overlap
  sels.append(m)
print('sel',len(sels))
import json
open(__import__('pathlib').Path(__file__).with_name('templates.json'),'w').write(json.dumps([(m,paths[m]) for m in sels]))
