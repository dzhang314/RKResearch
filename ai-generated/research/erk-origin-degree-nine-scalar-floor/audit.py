#!/usr/bin/env python3
from itertools import combinations_with_replacement,product
from math import lcm
from fractions import Fraction
rows=[]
for j in range(1,5):
    q=lcm(*(j+i+1 for i in range(6)))
    rows.append(tuple(q//(j+i+1)for i in range(6)))
assert rows==[(210,140,105,84,70,60),(280,210,168,140,120,105),
              (630,504,420,360,315,280),(504,420,360,315,280,252)]
def poly(T,m):
    p=[1]
    for u,v in T:
       out=[0]*(len(p)+1)
       for i,a in enumerate(p):
          out[i]-=a*u;out[i+1]+=a*v
       p=[a%m for a in out]
    return p
def good(T,m):
    return all(sum(a*b for a,b in zip(poly(T,m),r))%m==0 for r in rows)
for m in (2,4):
    R=[(u,1)for u in range(m)]+[(1,v)for v in range(0,m,2)]
    X=list(combinations_with_replacement(R,5))
    G=[p for p in X if good(p,m)]
    print("mod",m,"normalized projective multisets",len(X),"survivors",len(G),G)
    assert len(G)==(3 if m==2 else 0)
print("integer rows",rows)
