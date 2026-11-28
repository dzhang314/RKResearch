#!/usr/bin/env python3
"""Independent literal check of the two local ports and one genuine ghost."""
from fractions import Fraction as Q
from functools import cache
from math import lcm, prod
from pathlib import Path
import json

d=json.loads(Path(__file__).with_name("opening.json").read_text())
A=tuple(tuple(map(Q,row))+(Q(0),)*(9-len(row))for row in d["A"])
P=tuple(tuple(map(Q,row))for row in d["decoder"])
c=tuple(map(sum,A))
assert c[6:]==(Q(1),Q(1,3),Q(2,3))
assert all(not any(row[i:])for i,row in enumerate(A))
assert lcm(*(x.denominator for row in A for x in row))==d["matrix_denominator"]==1224720
assert lcm(*(x.denominator for row in P for x in row))==d["decoder_denominator"]==756
assert 1224720==2**4*3**7*5*7 and 756==2**2*3**3*7
def dot(a,b):return sum(x*y for x,y in zip(a,b))
@cache
def ts(n):
    if n==1:return ((),)
    choices=tuple((k,t)for k in range(1,n)for t in ts(k))
    def children(remaining,lo):
        if remaining==0:
            yield ();return
        for i in range(lo,len(choices)):
            k,t=choices[i]
            if k>remaining:break
            for rest in children(remaining-k,i):
                yield (t,)+rest
    return tuple(children(n-1,0))
@cache
def grad(t):return 1+sum(map(grad,t))
@cache
def trfac(t):return grad(t)*prod(map(trfac,t))
@cache
def phi(t):
    V=tuple(map(act,t))
    return tuple(prod(row[i]for row in V)for i in range(len(A))) if V else (Q(1),)*len(A)
@cache
def act(t):return tuple(dot(a,phi(t))for a in A)
for i,p,num in [(6,6,37),(7,5,17),(8,6,37)]:
    seen=0
    for n in range(1,p+1):
        for t in ts(n):
           assert phi(t)[i]*trfac(t)==n*c[i]**(n-1),(i,t)
           seen+=1
    assert seen==num
    print("physical row",i+1,"clock",c[i],"pure derivative profiles",seen)
t=((),(),(),())
assert act(t)[7]-c[7]**5/5==Q(11,4860)
assert act(t)[7]*3**5==Q(3,4)
print("first size-six ghost: child bush5, primitive defect 11/4860, normalized primitive 3/4")
seen=0
for n in range(1,6):
    for t in ts(n):
       assert tuple(dot(row,phi(t))for row in P)==tuple(Q(n,trfac(t))if j==n-1 else Q(0)for j in range(5))
       seen+=1
assert seen==17
for i in (6,7,8):
    assert tuple(sum(c[i]**k*P[k][j]for k in range(5))for j in range(9))==tuple(Q(i==j)for j in range(9))
print("decoder",seen,"rooted profiles, five coefficients each; three physical cardinal aliases")
