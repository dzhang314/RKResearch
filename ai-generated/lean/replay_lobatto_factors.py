#!/usr/bin/env python3
"""Independent standard-library arithmetic replay. Lean does not call this."""
from itertools import combinations
from math import comb, gcd, isqrt

def polyval(f, u, p):
    r = 0
    for a in reversed(f):
        r = (r*u+a) % p
    return r

def linprod(xs, p):
    f=[1]
    for x in xs:
        f=[((f[i-1] if i else 0)-x*(f[i] if i<len(f) else 0))%p
           for i in range(len(f)+1)]
    return f

for m,D,p,expected in [(7,4,1237,594),(8,5,1249,1533)]:
    assert p>=2 and all(p%d for d in range(2,isqrt(p)+1))
    # L_m has leading sign positive, value 1 at X=1.
    leg=[(-1)**(m+i)*comb(m,i)*comb(m+i,i) for i in range(m+1)]
    deriv=[i*leg[i] for i in range(1,m+1)]
    content=gcd(*deriv)
    assert content==m*(m+1)
    raw=[a//content for a in deriv]
    n=m-1
    c=raw[-1]
    H=[v*c**(n-i-1) for i,v in enumerate(raw[:-1])]+[1]
    roots=[x for x in range(p) if polyval(H,x,p)==0]
    assert len(roots)==n and 0 not in roots
    assert linprod(roots,p)==[a%p for a in H]
    hits=0
    for k in range(D+1):
        for subset in combinations([0]+roots,k):
            q=linprod(subset,p)
            for w in roots:
                assert sum((420//(i+2))*a*pow(w,i+2,p) for i,a in enumerate(q))%p
                hits+=1
    assert hits==expected
    print(f"m={m}: scale={c}, p={p}, H={H}, roots={roots}, all {hits} first moments nonzero")
