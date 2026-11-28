#!/usr/bin/env python3
"""Recursive Lucas/Pocklington primality witnesses, verified using only exact integers."""
from math import gcd,prod
from functools import lru_cache
PRIMES=(13, 59, 79, 83, 107, 1129, 6011194025914915991)
CERT={3: (2, ((2, 1),)),
 5: (2, ((2, 2),)),
 7: (3, ((2, 1), (3, 1))),
 11: (2, ((2, 1), (5, 1))),
 13: (2, ((2, 2), (3, 1))),
 23: (5, ((2, 1), (11, 1))),
 29: (2, ((2, 2), (7, 1))),
 41: (6, ((2, 3), (5, 1))),
 47: (5, ((2, 1), (23, 1))),
 53: (2, ((2, 2), (13, 1))),
 59: (2, ((2, 1), (29, 1))),
 79: (3, ((2, 1), (3, 1), (13, 1))),
 83: (2, ((2, 1), (41, 1))),
 107: (2, ((2, 1), (53, 1))),
 277: (5, ((2, 2), (3, 1), (23, 1))),
 313: (10, ((2, 3), (3, 1), (13, 1))),
 1129: (11, ((2, 3), (3, 1), (47, 1))),
 9391: (3, ((2, 1), (3, 1), (5, 1), (313, 1))),
 7505593: (5, ((2, 3), (3, 1), (277, 1), (1129, 1))),
 1404484585494139: (2, ((2, 1), (3, 5), (41, 1), (9391, 1), (7505593, 1))),
 5617938341976557: (2, ((2, 2), (1404484585494139, 1))),
 6011194025914915991: (17, ((2, 1), (5, 1), (107, 1), (5617938341976557, 1)))}
@lru_cache(None)
def certify(n):
    if n==2:return True
    assert n%2==1 and n>=3
    a,factors=CERT[n]
    assert 1<a<n
    assert len(set(q for q,e in factors))==len(factors)
    assert all(e>0 and 2<=q<n and certify(q) for q,e in factors)
    assert prod(q**e for q,e in factors)==n-1
    assert pow(a,n-1,n)==1
    assert all(gcd(pow(a,(n-1)//q,n)-1,n)==1 for q,e in factors)
    return True
if __name__=='__main__':
    for p in PRIMES:
        assert certify(p)
        print('certified prime',p)
