#!/usr/bin/env python3
"""Exact residue checks of the clock-only cuts, independent of tableau data."""
from itertools import permutations

P = 227
interior = tuple(x for x in range(P) if (42*x**4-84*x**3+56*x**2-14*x+1) % P == 0)
assert interior == (24, 51, 177, 204)
nonzero = (*interior, 1)
triples = tuple(permutations(nonzero, 3))
assert len(triples) == 60
for a, b, u in triples:
    assert (u*(4*a*b-a*a-b*b)-a*b*(a+b)) % P, (a,b,u)
    assert ((a+b-u) % P or (5*a*b-u*u) % P), (a,b,u)
    assert (10*a*b-5*(a+b)*u+3*u*u) % P, (a,b,u)
print(f"mod {P}: all {len(triples)} distinct ordered nonzero Lobatto triples pass both tests")

quartets = tuple(permutations(nonzero, 4))
assert len(quartets) == 120
for a,b,c,x in quartets:
    s1, s2, s3 = a+b+c, a*b+a*c+b*c, a*b*c
    primitive60 = (10*x**6-12*(s1+x)*x**5+15*(s2+x*s1)*x**4
                   -20*(s3+x*s2)*x**3+30*s3*x**3)
    assert primitive60 % P, (a,b,c,x)
print(f"mod {P}: all {len(quartets)} distinct ordered nonzero Lobatto quartets pass the quintic test")

def quartic_primitive_60(v, x):
    r = [1]
    for u in v:
        r = [(-u * (r[k] if k < len(r) else 0) + (r[k-1] if k else 0)) % P
             for k in range(len(r)+1)]
    return sum((60 // (i+1)) * c * x**(i+1) for i,c in enumerate(r)) % P

for a,x in permutations(nonzero, 2):
    assert (5*a*(x-a)-x*x) % P, (a,x)
for a,b,x in triples:
    d = (3*x*x - 5*(a+b)*x + 10*a*b) % P
    q = x*(2*x*x - 3*(a+b)*x + 5*a*b) * pow(d,-1,P) % P
    donor = (0,a,b,q,x)
    for k in range(5):
        assert quartic_primitive_60(donor[:k]+donor[k+1:], x), (a,b,x,q,k)
print(f"mod {P}: all {len(triples)} fixed triple one-off candidates have five nonzero taps")
