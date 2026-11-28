#!/usr/bin/env python3
"""Exact minimal rooted-source spans for the literal dirty relay."""
from pathlib import Path
from fractions import Fraction as F
import json,sys
from math import prod
from functools import cache
fn=Path(__file__).resolve().parent.parent/"erk10-dirty-sixth-relay"/"opening.json"
d=json.loads(fn.read_text())
A=[list(map(F,r))+[F(0)]*(9-len(r))for r in d["A"]]
P=[list(map(F,r))for r in d["decoder"]]
c=list(map(sum,A))
@cache
def size(t):return 1+sum(map(size,t))
@cache
def fac(t):return size(t)*prod(map(fac,t))
def dot(a,b):return sum(x*y for x,y in zip(a,b))
@cache
def phi(t):return [prod(X[i]for X in map(act,t))for i in range(9)]
@cache
def act(t):return [dot(a,phi(t))for a in A]
def residual(t):
    n=size(t)
    f=[-dot(r,phi(t))for r in P]+[F(0)]*(n-5)
    f[-1]+=F(n,fac(t))
    return f
sources=[((),)*5,((),((),)*3),(((),)*4,)]
sources += [((),)*(k-1)for k in (7,8,9)]
L=list(map(residual,sources))
E=lambda f,x:sum(v*x**j for j,v in enumerate(f))
for f,t in zip(L,sources):
    assert max(map(size,t))<=5
    assert all(E(f,x)==0 for x in (F(0),F(1),F(2,3)))
    print("source size",size(t),"polynomial",[str(x)for x in f])
f,g,h=[r[1:4]for r in L[:3]]
D=f[0]*(g[1]*h[2]-g[2]*h[1])-f[1]*(g[0]*h[2]-g[2]*h[0])+f[2]*(g[0]*h[1]-g[1]*h[0])
assert D==F(11,1728)
assert all(r[-1]==1 for r in L[3:])
for i in (6,8):
        x=c[i]
        assert tuple(sum(x**(k+1)*P[k][j]/(k+1)for k in range(5))for j in range(9))==tuple(A[i])
print("size-six coefficient minor",D,"and higher bush monic heads 6,7,8")
print("physical FSAL and relay both equal integrated decoder rows")
