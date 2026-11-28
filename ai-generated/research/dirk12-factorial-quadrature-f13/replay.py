#!/usr/bin/env python3
"""Exact polynomial template and all 13 scalar score supports."""
from collections import defaultdict
p=13
w=[sum(pow(a,k,p)*pow(k,-1,p) for k in range(1,p))%p for a in range(p)]
L=defaultdict(list)
for a in range(p):L[w[a]].append(a)
assert w==[0,0,7,8,0,6,4,3,4,6,0,8,7]
print("rho =",w)
print("multiplicities =",sorted(L.items()))
for theta in range(p):
    assert all(sum((theta+c)*pow(a,j,p) for a,c in enumerate(w))%p==pow(j+1,-1,p)
               for j in range(p-1))
    support={a for a,c in enumerate(w) if (c+theta)%p}
    assert len(support|{0,1})>=11
    print("theta",theta,"required anchor-containing label count:",len(support|{0,1}))
print("unique fixed-anchor support floor 11 holds for all 13 scores")
