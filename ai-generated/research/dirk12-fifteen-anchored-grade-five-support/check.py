#!/usr/bin/env python3
"""Exact shifted-Legendre and finite nonvanishing receipts."""
from itertools import combinations
from fractions import Fraction as Q

L=[1,-42,420,-1680,3150,-2772,924]
H=[i*a for i,a in enumerate(L)]
for j in range(6):
    assert sum(Q(a,i+j+1)for i,a in enumerate(L))==0
    assert sum(Q(a,i+j+1)for i,a in enumerate(H))==1
assert sum(L)==1 and sum(H)==42
p=43
def ev(f,z):return sum(a*pow(z,j,p)for j,a in enumerate(f))%p
roots=[z for z in range(p)if ev(H,z)==0]
assert roots==[0,2,9,22,35,42] and H[-1]%p and 1 not in roots
def P(a,b,c):return [-a*b*c,a*b+a*c+b*c,-(a+b+c),1]
def diff(q,z):return sum(-60//((j+2)*(j+3))*a*pow(z,j+3,p)for j,a in enumerate(q))%p
def J2(q,z):return sum(60//(j+3)*a*pow(z,j+3,p)for j,a in enumerate(q))%p
counts=[0,0,0,0]
for A in combinations(roots,3):
    q=P(*A)
    for u in roots:
        if not u or u in A:continue
        assert diff(q,u) and J2(q,u)
        counts[0]+=1
    assert J2(q,1)
    counts[1]+=1
    counts[2]+=not bool(diff(q,1))
    counts[3]+=sum(1 for t in roots+[1] if t and t not in A and J2(q,t))
assert counts==[50,20,2,70],counts
print("Six Legendre/Jacobi moment rows; six distinct H roots mod43.")
print("Nonterminal diagonal-eliminated tests 50/50; terminal pure x² tests 20/20.")
print("Unrefunded terminal formula has 2 exceptions; pure x² all 70/70.")
