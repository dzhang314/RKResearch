#!/usr/bin/env python3
"""Exact finite scalar-span checks and two-minor unit receipts."""
import contextlib,io,json,runpy
from fractions import Fraction as F
from functools import cache
from math import prod
from pathlib import Path
Z,O=F(0),F(1)
ROOT=Path(__file__).resolve().parent.parent
with contextlib.redirect_stdout(io.StringIO()):
    shanks=runpy.run_path(str(ROOT/"erk-eight-ring-witness"/"check.py"))
@cache
def ts(n):
    if n==1:return ((),)
    all_=tuple((k,t)for k in range(1,n)for t in ts(k))
    def rec(n,start):
        if not n:
            yield ();return
        for i in range(start,len(all_)):
            k,t=all_[i]
            if k>n:break
            for r in rec(n-k,i):yield (t,)+r
    return tuple(rec(n-1,0))
def dot(x,y):return sum(a*b for a,b in zip(x,y))
def builder(A):
 @cache
 def phi(t):
    D=tuple(map(act,t))
    return tuple(prod(a[i]for a in D)for i in range(len(A)))if D else (O,)*len(A)
 @cache
 def act(t):return tuple(dot(r,phi(t))for r in A)
 return phi
def det(rows):
 A=[list(map(F,r))for r in rows]; d=O;n=len(A)
 for k in range(n):
  j=next((j for j in range(k,n)if A[j][k]),None)
  if j is None:return Z
  if j!=k:A[j],A[k]=A[k],A[j];d=-d
  q=A[k][k];d*=q
  for j in range(k+1,n):
   r=A[j][k]/q;A[j]=[a-r*b for a,b in zip(A[j],A[k])]
 return d
def space(rows,n):
 M={}
 for r in rows:
  r=list(map(F,r))
  for i,v in enumerate(r):
   if not r[i]:continue
   if i not in M:
    z=r[i];M[i]=[a/z for a in r];break
   z=r[i];r=[a-z*b for a,b in zip(r,M[i])]
 q=[]
 for j in range(n):
  if j in M:continue
  x=[Z]*n;x[j]=O
  for i in sorted(M,reverse=True):x[i]=-dot(M[i][i+1:],x[i+1:])
  q.append(x)
 return q

common=[(1,0),(2,0),(3,0),(3,1),(4,0),(4,3),(5,0),(5,5),(5,8),(6,0)]
kinds=[
 ("original",[common+[(6,11)],common+[(6,16)]],
  [F(1127,5180630263231634472960000),F(2429,12433512631755922735104000)],(-125,58),(2,3,5,7,41)),
 ("adapted",[common+[(6,11),(6,16)],common+[(6,11),(6,19)]],
  [F(-6839,655033836209580319703040000),F(-4781,436689224139720213135360000)],(151,-216),(2,3,5,7)),
]
for name,S,ex,bez,pay in kinds:
 A,b=shanks[name+"_A"],shanks[name+"_b"];phi=builder(A)
 c=tuple(map(sum,A));n=len(A);columns=[i for i in range(n)if i!=10]
 assert c[9]==c[10]==F(5,6)
 assert all(phi(t)[9]==phi(t)[10]for m in range(1,7)for t in ts(m))
 ds=[det([[phi(ts(m)[j])[i]for i in columns]for m,j in s])for s in S]
 assert ds==ex
 for d in ds:
  n0=d.denominator
  for p in pay:
   while n0%p==0:n0//=p
  assert n0==1
 assert sum(a*d.numerator for a,d in zip(bez,ds))==7
 defect=9*dot(b,phi(((),)*8))-1
 assert defect==F(1,4320)
 print("Shanks",name,len(A),"tree bases",S)
 print("minors",list(map(str,ds)),"Bézout",bez,"give 7; ninth bush",defect)
for p,names in [(8,["erk-eight-dispersed","erk-eight-rank3-four"]),
                (9,["erk9-fourteen-rational-triple","erk9-fourteen-field-portfolio"])]:
 for name in names:
  d=json.loads((ROOT/name/"tableau.json").read_text())
  A=[tuple(map(F,r))for r in d["A"]]; b=list(map(F,d["b"]))
  c=list(map(sum,A));f=builder(A);n=len(A)
  S=space([f(t)for q in range(1,p-2+1)for t in ts(q)],n)
  assert len(S)==1
  assert all(sum(a for a,y in zip(v,c)if y==x)==0 for v in S for x in set(c))
  defect=(p+1)*dot(b,f(((),)*p))-1
  assert defect
  print(name,n,"size",p-2,"rank",n-len(S),"annihilator",list(map(str,S[0])),"next bush",defect)
