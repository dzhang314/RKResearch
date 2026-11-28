#!/usr/bin/env python3
"""Exact Jacobi causal and integral receipts: the analytic lifting is in README."""
from fractions import Fraction as Q
from itertools import permutations
H=[0,1,-14,56,-84,42]
def h(x):return sum(a*x**i for i,a in enumerate(H))
def intH(j):return sum(Q(a,i+j+1)for i,a in enumerate(H))
assert [intH(j)for j in range(5)]==[Q(1,30)]*5
z=[Q(i,6)for i in (-1,1,2,3,4,5)]
L=[]
for u,p in permutations(z,2):
    val=u**3*(2*p-u)*h(p)-p**3*(2*u-p)*h(u)
    assert val
    L.append(val)
assert len(L)==30
print("Five Jacobi moments = 1/30; all 30 exact ordered causal differences nonzero.")
