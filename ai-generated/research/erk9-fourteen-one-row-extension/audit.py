#!/usr/bin/env python3
"""Independent exact rank and bush check of the fixed fourteen-stage seed."""
from fractions import Fraction as F
from functools import cache
from math import prod
from pathlib import Path
import json
@cache
def trees(n):
    if n==1:return ((),)
    choices=tuple((m,t)for m in range(1,n)for t in trees(m))
    def child(k,start):
        if not k:
            yield ();return
        for i in range(start,len(choices)):
            m,t=choices[i]
            if m>k:break
            for rest in child(k-m,i):
                yield (t,)+rest
    return tuple(child(n-1,0))
@cache
def size(t):return 1+sum(map(size,t))
@cache
def factorial(t):return size(t)*prod(map(factorial,t))
def dot(a,b):return sum(x*y for x,y in zip(a,b))
R=Path(__file__).resolve().parent.parent/'erk9-fourteen-rational-triple'/'tableau.json'
d=json.loads(R.read_text()); n=14
A=[tuple(map(F,r))+(F(0),)*(n-len(r))for r in d['A']]
b=list(map(F,d['b']))
assert len(A)==len(b)==n and all(not any(r[i:])for i,r in enumerate(A))
@cache
def phi(t):
    V=tuple(map(act,t))
    return tuple(prod(x[i]for x in V)for i in range(n))if V else (F(1),)*n
@cache
def act(t):return tuple(dot(r,phi(t))for r in A)
def det(U):
    A=list(map(list,U)); D=F(1);n=len(A)
    for i in range(n):
        j=next((j for j in range(i,n)if A[j][i]),None)
        if j is None:return F(0)
        if j!=i:
           A[i],A[j]=A[j],A[i];D=-D
        z=A[i][i];D*=z
        for j in range(i+1,n):
            w=A[j][i]/z
            A[j]=[a-w*b for a,b in zip(A[j],A[i])]
    return D
I=[(1,0),(2,0),(3,0),(3,1),(4,0),(4,2),(5,0),(5,5),(5,7),(6,0),(6,5),(6,11),(7,28),(8,95)]
S=[trees(n)[j]for n,j in I]
M=[phi(t)for t in S]
D=det(M)
assert D==F(-699914663248933,613702752390000000000000000000000000000)
m=29
red=lambda a:a.numerator*pow(a.denominator,-1,m)%m
assert red(D)==5
print('basis (tree size, zero-based enumeration index)',I)
print('literal tree shapes',S)
print('rational determinant',D)
print('determinant mod 29',red(D))
print('literal mod-29 profile matrix',[list(map(red,row))for row in M])
ncheck=0
for k in range(1,10):
    for t in trees(k):
        assert factorial(t)*dot(b,phi(t))==1
        ncheck+=1
assert ncheck==486
D1=10*dot(b,phi(((),)*9))-1
assert D1==F(-1,2160)
print('ordinary rooted order-nine equalities',ncheck,'normalized tenth-order bush defect',D1)
