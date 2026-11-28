#!/usr/bin/env python3
"""Direct integer replay and the exact combined denominator test."""
from fractions import Fraction as Q
from functools import cache
from math import gcd, lcm, prod
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parent
paths=['../erk10-sixteen-rational-mirror/tableau.json','theta-five-fourths.json',
       'denominator-unit-at-11.json','denominator-unit-at-13.json','theta-four.json']

@cache
def trees(n):
    if n==1:
        return ((),)
    choices=[(k,t) for k in range(1,n) for t in trees(k)]
    def tails(start,left):
        if not left:
            yield ()
        else:
            for i in range(start,len(choices)):
                k,t=choices[i]
                if k>left:break
                for r in tails(i,left-k):yield (t,)+r
    return tuple(tails(0,n-1))

@cache
def size(t):return 1+sum(map(size,t))

@cache
def tf(t):return size(t)*prod(map(tf,t))

def check(name):
    j=json.loads((ROOT/name).read_text())
    A=[list(map(Q,row)) for row in j['A']]
    b=list(map(Q,j['b']))
    assert len(A)==len(b)==16 and all(len(row)==i for i,row in enumerate(A))
    assert len({tuple(row+[Q(0)]*(16-len(row))) for row in A})==16
    D=lcm(*(v.denominator for a in A for v in a),*(v.denominator for v in b))
    assert D==int(j['denominator'])
    A=[tuple(int(D*v) for v in a) for a in A]
    b=tuple(int(D*v) for v in b)
    @cache
    def stage(t):
        return tuple(prod(advance(u)[i] for u in t) for i in range(16))
    @cache
    def advance(t):
        vec=stage(t)
        return tuple(sum(a*vec[k] for k,a in enumerate(row)) for row in A)
    def numerator(t):
        return tf(t)*sum(x*y for x,y in zip(b,stage(t)))
    counts=[]
    for n in range(1,11):
        ts=trees(n)
        assert all(numerator(t)==D**n for t in ts)
        counts.append(len(ts))
    assert counts==[1,1,2,4,9,20,48,115,286,719]
    t1=((),)*10
    t2=((),)*4+(((),)*5,)
    e1,e2=[Q(numerator(t),D**11)-1 for t in (t1,t2)]
    assert size(t1)==size(t2)==11 and e1==Q(j['next_failure_value'])
    assert gcd(e1.numerator,e2.numerator)==1
    print(name,'distinct stages',len(A),'rooted conditions',sum(counts),'defects',e1,e2)
    return D

ds=[check(name) for name in paths]
assert ds[2]%11 and ds[3]%13
g=gcd(*ds)
print('gcd of the five coefficient denominators:',g)
for p in (2,3,5,7):
    while g%p==0:g//=p
assert g==1
print('No common denominator prime outside 10!.')
