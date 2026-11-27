#!/usr/bin/env python3
"""Exact rational moment and modular Lobatto receipts."""
from fractions import Fraction as F
from itertools import permutations, product

def det(n, off):
    m=[[F(1,(i+j+off)*(i+j+off+1)) for j in range(n)] for i in range(n)]
    d=F(1)
    for i in range(n):
        d*=m[i][i]
        for j in range(i+1,n):
            r=m[j][i]/m[i][i]
            for k in range(i,n):
                m[j][k]-=r*m[i][k]
    return d

assert det(5,1)==F(1,67212633600000)
assert det(4,2)==F(1,53343360000)
p=(1,-14,56,-84,42)
for j in range(4):
    assert sum(F(a,(i+j+2)*(i+j+3)) for i,a in enumerate(p))==0
for j in range(5):
    from math import comb
    assert sum(a*comb(i,j)*(-1)**j for i,a in enumerate(p) if i>=j)==p[j]

prime=227
assert all(prime%i for i in range(2,16))
roots=[x for x in range(prime) if sum(a*x**j for j,a in enumerate(p))%prime==0]
assert roots==[24,51,177,204]
assert all(sum(j*a*x**(j-1) for j,a in enumerate(p) if j)%prime for x in roots)
assert all((2*t-3*a)%prime for t,a in product(roots,repeat=2))
assert all((6*a*b-4*(a+b)*t+3*t*t)%prime for a,b in permutations(roots,2) for t in roots)
print("Five-/four-dimensional Beta determinants and the Lobatto polynomial verified.")
print("Modulo 227: four simple roots, all 16 ratio tests and all 48 two-donor cubic tests nonzero.")
