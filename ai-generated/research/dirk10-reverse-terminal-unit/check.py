#!/usr/bin/env python3
"""Integral receipts for the factorial-localized five-site scalar support gate."""
from fractions import Fraction
from math import prod

D=2520
H=[[D//(i+j+1) for j in range(5)]for i in range(5)]
B=[
    [25,-300,1050,-1400,630],
    [-300,4800,-18900,26880,-12600],
    [1050,-18900,79380,-117600,56700],
    [-1400,26880,-117600,179200,-88200],
    [630,-12600,56700,-88200,44100],
]
L=[-1,30,-210,560,-630,252]
def mul(a,b):return [[sum(x*y for x,y in zip(r,c))for c in zip(*b)]for r in a]
assert all(D%(j+1)==0 for j in range(10))
assert prod(range(1,11))%D==0
assert mul(H,B)==mul(B,H)==[[D*(i==j)for j in range(5)]for i in range(5)]
assert all(sum(l*Fraction(1,i+j+1)for i,l in enumerate(L))==0 for j in range(5))
assert all(sum(l*(D//(i+j+1))for i,l in enumerate(L))==0 for j in range(5))
assert L[0]==-1 and L[-1]==252 and D%252==0
print("2520-cleared integral inverse; five orthogonalities; constant -1/252.")
