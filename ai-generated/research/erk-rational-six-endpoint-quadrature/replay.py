#!/usr/bin/env python3
"""Independent exact rational moments and finite split polynomials."""
from fractions import Fraction as F
from itertools import permutations

def sg(p):return -1 if sum(x>y for i,x in enumerate(p)for y in p[i+1:])%2 else 1
B=[[F(1,(i+j+2)*(i+j+3))for j in range(3)]for i in range(3)]
assert sum(sg(p)*B[0][p[0]]*B[1][p[1]]*B[2][p[2]]for p in permutations(range(3)))==F(1,1512000)
L3=[-1,9,-21,14];L4=[1,-14,56,-84,42]
for a in (L3,L4):
    for j in range(3):
        assert sum(F(c,(i+j+2)*(i+j+3))for i,c in enumerate(a))==0
def peel(f,r,p=11):
    q=[0]*(len(f)-1)
    a=f[-1]%p
    for i in reversed(range(1,len(f))):
        q[i-1]=a
        a=(f[i-1]+a*r)%p
    return (q,a)
def degree_left(f):
    for r in range(11):
        while len(f)>1:
            q,g=peel(f,r)
            if g:break
            f=q
    return len(f)-1
counts=[]
for v in range(11):
    f=[a+v*b for a,b in zip(L4,L3+[0])]
    counts.append(degree_left(f))
assert all(counts)
assert degree_left(L3)==2
print("Residual degrees in the 11 finite pencil members:",counts)
print("Residual cubic degree in the projective-infinity member:",degree_left(L3))
