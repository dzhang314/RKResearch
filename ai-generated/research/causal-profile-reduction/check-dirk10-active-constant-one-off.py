#!/usr/bin/env python3
"""Independent scalar replay for the three ghost heads."""
from itertools import permutations

p = 419
roots = tuple(x for x in range(p) if (42*x**4-84*x**3+56*x*x-14*x+1) % p == 0)
assert roots == (67,141,279,353)
fixed = (*roots,1)


def div(a,b):
    assert b % p
    return a * pow(b % p,-1,p) % p


def pair(a,b,u):
    return (u*(4*a*b-a*a-b*b)-a*b*(a+b)) % p


def primitive(nodes,x):
    q = [1]
    for z in nodes:
        q = [((q[i-1] if i else 0)-z*(q[i] if i < len(q) else 0)) % p
             for i in range(len(q)+1)]
    return sum(div(c*x**(i+1),i+1) for i,c in enumerate(q)) % p


for a,b,u in permutations(fixed,3):
    assert pair(a,b,u)
for a,u in permutations(fixed,2):
    q = div(u*(4*a-3*u),6*a-4*u)
    assert pair(a,q,u)
    assert (5*a*(u-a)-u*u) % p
n = 0
for tau,x in permutations(roots,2):
    q = div(x*(2*x*x-3*(tau+1)*x+5*tau),3*x*x-5*(tau+1)*x+10*tau)
    labels = (0,1,tau,q,x)
    assert len(set(labels)) == 5
    for v in (q,tau,1):
        others = tuple(j for j in labels if j != v)
        d = 1
        for j in others:
            d = d*(v-j) % p
        assert div(primitive(others,x),d)
    for a,b,u in permutations((q,tau,1)):
        assert pair(a,b,u), (tau,x,q,a,b,u)
        n += 1
assert n == 72
print(f"mod {p}: all 72 ghost-head orders excluded; fixed-pair and tap guards checked")
