#!/usr/bin/env python3
"""Read literal lifts only; use independently ordered tree multisets."""
from functools import cache
from math import prod
from pathlib import Path
import json
HERE=Path(__file__).resolve().parent
data=json.loads((HERE/'literal-geometry-lifts.json').read_text())
base=json.loads((HERE.parent/'erk10-fifteen-f17'/'tableau.json').read_text())
@cache
def order(t):return 1+sum(order(v)for v in t)
@cache
def density(t):return order(t)*prod(density(v)for v in t)
@cache
def forests(n,t):
    if n==0:return ((),)
    return tuple((s,)+q for i in range(order(t),n+1)for s in trees(i)
                 if i>order(t) or s>=t for q in forests(n-i,s))
@cache
def trees(n):return forests(n-1,())
last=None
for k,s in sorted(data.items(),key=lambda t:int(t[0])):
    m=s['mod']
    assert m==17**int(k)
    A=s['a'];b=s['b']
    assert len(A)==len(b)==15 and all(len(r)==i for i,r in enumerate(A))
    assert all(0<=x<m for r in A for x in r) and all(0<=x<m for x in b)
    if last:
        z=m//17
        assert [[x%z for x in r]for r in A]==last['a'] and [x%z for x in b]==last['b']
    else:assert A==base['A'] and b==base['b']
    @cache
    def stage(t):
        ps=tuple(incoming(u)for u in t)
        return tuple(prod(u[i]for u in ps)%m for i in range(15))
    @cache
    def incoming(t):
        u=stage(t)
        return tuple(sum(x*y for x,y in zip(r,u))%m for r in A)
    counts=[len(trees(i))for i in range(1,11)]
    assert counts==[1,1,2,4,9,20,48,115,286,719]
    for n in range(1,11):
        for t in trees(n):
            assert density(t)*sum(x*y for x,y in zip(b,stage(t)))%m==1,(k,n,t)
    t=((),)*10
    ne=(11*sum(x*y for x,y in zip(b,stage(t)))-1)%m
    assert ne==s['next_failure'][1] and ne%17==8
    print('power',k,'strict',15,'all ordinary checks',sum(counts),'unit eleventh bush defect',ne)
    last=s
