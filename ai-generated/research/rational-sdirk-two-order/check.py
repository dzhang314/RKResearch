from fractions import Fraction as F
from pathlib import Path
from functools import cache
from math import prod
import json,sys
for p,n,moment in [(8,13,F(-1245689,697374720)),(9,19,F(-87763,12965400)),(10,21,F(-2432737,1580146360320))]:
 d=json.loads(Path(sys.argv[1],f'tableau-{p}.json').read_text())
 A=tuple(tuple(map(F,x)) for x in d['A']); b=tuple(map(F,d['b']))
 assert len(A)==len(b)==n and all(len(r)==n and not any(r[i+1:]) for i,r in enumerate(A))
 gam=F(d['common_diagonal'])
 assert gam and all(A[i][i]==gam for i in range(n))
 A=tuple(tuple((j,a) for j,a in enumerate(r) if a) for r in A)
 ts={1:[()]}; old=[(1,())]
 @cache
 def parts(rem,j=0):
  if rem==0:return [()]
  return [(t,)+rest for k in range(j,len(frozen)) for s,t in [frozen[k]] if s<=rem for rest in parts(rem-s,k)]
 for k,want in enumerate([1,1,2,4,9,20,48,115,286,719][:p],1):
  if k>1:
   frozen=tuple(old);parts.cache_clear()
   ts[k]=parts(k-1);old.extend((k,t) for t in ts[k])
  assert len(ts[k])==len(set(ts[k]))==want
 @cache
 def response(t):
  ps=[response(u) for u in t];s=1+sum(x[0] for x in ps)
  return s,s*prod(x[1] for x in ps),[prod(sum(a*h[2][j] for j,a in r) for h in ps) for r in A]
 def defect(t):
  _,f,v=response(t);return f*sum(x*y for x,y in zip(b,v))-1
 assert all(not defect(t) for tree_list in ts.values() for t in tree_list)
 nxt=defect(((),)*p)
 assert nxt==-(p+1)*moment and nxt
 print(f'order {p}: {n} diagonal-{gam} rows, {len(old)} tree equations, next bush {nxt}')
