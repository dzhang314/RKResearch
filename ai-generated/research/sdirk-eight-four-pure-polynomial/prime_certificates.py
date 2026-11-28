#!/usr/bin/env python3
"""Recursive Lucas/Pocklington primality witnesses, verified using only exact integers."""
from math import gcd,prod
from functools import lru_cache
PRIMES=(770514337, 26254266039604698273071)
CERT={3: (2, ((2, 1),)),
 5: (2, ((2, 2),)),
 7: (3, ((2, 1), (3, 1))),
 11: (2, ((2, 1), (5, 1))),
 13: (2, ((2, 2), (3, 1))),
 29: (2, ((2, 2), (7, 1))),
 53: (2, ((2, 2), (13, 1))),
 59: (2, ((2, 1), (29, 1))),
 107: (2, ((2, 1), (53, 1))),
 281: (3, ((2, 3), (5, 1), (7, 1))),
 563: (2, ((2, 1), (281, 1))),
 2663: (5, ((2, 1), (11, 3))),
 4721: (6, ((2, 4), (5, 1), (59, 1))),
 10891: (2, ((2, 1), (3, 2), (5, 1), (11, 2))),
 148633: (15, ((2, 3), (3, 1), (11, 1), (563, 1))),
 820691: (7, ((2, 1), (5, 1), (13, 1), (59, 1), (107, 1))),
 891799: (3, ((2, 1), (3, 1), (148633, 1))),
 4924147: (2, ((2, 1), (3, 1), (820691, 1))),
 770514337: (7, ((2, 5), (3, 3), (891799, 1))),
 1914180379: (3, ((2, 1), (3, 1), (11, 1), (2663, 1), (10891, 1))),
 26254266039604698273071: (11, ((2, 1), (5, 1), (59, 1), (4721, 1), (4924147, 1), (1914180379, 1)))}
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
