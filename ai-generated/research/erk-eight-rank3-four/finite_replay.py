#!/usr/bin/env python3
"""Literal all-tree modular checks; independent of how the data were found."""
from fractions import Fraction
from functools import cache
from math import gcd, prod
from pathlib import Path
import json
from replay import D, T, factorial

primes=[11,13,19,23,29,41,53,89,103,173,397,409,449,607,1319,4813,
        8053,50159,56941,60961,367841,2120099,20627713,1714218151]
def isprime_trial(p):
    i=2
    while i*i<=p:
        if p%i==0: return False
        i += 1 if i==2 else 2
    return p>=2

assert all(isprime_trial(p) for p in primes)
remaining = D
for p in [2,3,5,7,*primes]:
    assert remaining%p==0
    while remaining%p==0:
        remaining//=p
assert remaining==1
data=json.loads(Path(__file__).with_name('finite-prime-tableaux.json').read_text())
assert [a['p'] for a in data]==primes
for a in data:
    p=a['p']
    M,b = a['A'],a['b']
    assert len(M)==len(b)==11 and [len(row) for row in M]==list(range(11))
    assert all(0<=z<p for row in M for z in row) and all(0<=z<p for z in b)
    @cache
    def state(t):
        if not t: return (1,)*11
        v,u=t[0],t[1:]
        x,y=state(v),state(u)
        return tuple(y[i]*sum(m*z for m,z in zip(M[i],x))%p for i in range(11))
    def pay(t):
        return factorial(t)*sum(x*y for x,y in zip(state(t),b))%p
    for n in range(1,9):
        for t in T[n]:
            assert pay(t)==1,(p,n,t)
    assert any(pay(t)!=1 for t in T[9])
    assert (pay(((),)*8)-1)%p==a['bush9']
print('All 24 exceptional-prime tableaus independently checked: 4,800 order identities plus exactness.')
