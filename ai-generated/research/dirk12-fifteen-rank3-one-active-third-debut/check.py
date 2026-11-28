#!/usr/bin/env python3
"""Small, independent fixed-coefficient arithmetic for the two chronological gates."""
from itertools import permutations

P = 1013
D6 = (-42, 840, -5040, 12600, -13860, 5544)
INTERIORS = (347, 468, 507, 546, 667)
LIVE = (*INTERIORS, 1)


def value(f, z):
    r = 0
    for a in reversed(f):
        r = (a + z*r) % P
    return r


def main():
    assert all(P % k for k in range(2,32))
    assert D6[-1] % P != 0
    assert tuple(z for z in range(P) if value(D6,z)==0) == INTERIORS
    assert len(set((0,*LIVE)))==7
    pairs = [(a,b) for a,b in permutations(LIVE,2)
             if (10*b*b-12*a*b+3*a*a) % P != 0]
    triples = [(a,b,u) for a,b,u in permutations(LIVE,3)
               if (3*u*u-5*(a+b)*u+10*a*b) % P != 0]
    assert len(pairs)==30 and len(triples)==120
    print("mod 1013: 30 ordered Radau ratios and 120 ordered nodal triples are excluded")


if __name__=="__main__":
    main()
