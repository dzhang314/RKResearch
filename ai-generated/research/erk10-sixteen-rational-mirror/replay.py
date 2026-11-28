#!/usr/bin/env python3
"""Exact direct order replay with one global integer denominator."""
from fractions import Fraction as Q
from functools import cache
from math import gcd, isqrt, lcm, prod
import json
from pathlib import Path

D0=Path(__file__).resolve().parent
J=json.loads((D0/'tableau.json').read_text())
A=[list(map(Q,row)) for row in J['A']]
b=list(map(Q,J['b']))
assert len(A)==len(b)==16 and all(len(a)==i for i,a in enumerate(A))
assert len({tuple(a+[Q(0)]*(16-len(a))) for a in A})==16
D=lcm(*(a.denominator for row in A for a in row),*(x.denominator for x in b))
assert D==int(J['denominator'])
factors={int(p):e for p,e in json.loads((D0/'denominator-factors.json').read_text()).items()}
assert prod(p**e for p,e in factors.items())==D
assert all(all(p%d for d in range(2,isqrt(p)+1)) for p in factors)
A=[tuple(int(D*x) for x in a) for a in A]
b=tuple(int(D*x) for x in b)

@cache
def trees(n):
    if n==1:
        return ((),)
    bucket=[(k,t) for k in range(1,n) for t in trees(k)]
    def tails(start,left):
        if not left:
            yield ()
        else:
            for i in range(start,len(bucket)):
                k,t=bucket[i]
                if k>left:break
                for r in tails(i,left-k):yield (t,)+r
    return tuple(tails(0,n-1))

@cache
def size(t):
    return 1+sum(map(size,t))

@cache
def tf(t):
    return size(t)*prod(map(tf,t))

@cache
def stage(t):
    return tuple(prod(advance(u)[i] for u in t) for i in range(16))

@cache
def advance(t):
    v=stage(t)
    return tuple(sum(x*v[j] for j,x in enumerate(row)) for row in A)

def numerator(t):
    return tf(t)*sum(x*y for x,y in zip(b,stage(t)))

counts=[]
for n in range(1,11):
    ts=trees(n)
    assert all(numerator(t)==D**n for t in ts)
    counts.append(len(ts))
assert counts==[1,1,2,4,9,20,48,115,286,719]
leaves=()
star=(leaves,)*10
second=(leaves,)*4+((leaves,)*5,)
def defect(t):
    assert size(t)==11
    return Q(numerator(t),D**11)-1
e1,e2=defect(star),defect(second)
assert e1==Q(J['next_failure_value'])==Q(-44183114898821,88516189142307000)
assert e2==Q(-506482972805483195311,82783211226952318425000)
assert gcd(e1.numerator,e2.numerator)==1
print('16 strict, pairwise distinct stages; 1205 ordinary rooted conditions')
print('common denominator:',D)
print('two normalized defects:',e1,e2,'with coprime numerators')
