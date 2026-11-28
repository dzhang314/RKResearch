"""Exact constant and Gauss reverse-root checks in the sibling proof tree."""
from pathlib import Path
import sys
root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic","sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-three-closure","sdirk-eight-silent-two-unequal",
            "sdirk-eight-silent-two-equal","sdirk-eight-silent-two-high",
            "sdirk-eight-silent-one-seven-six-anchored",
            "sdirk-eight-silent-one-seven-six-reverse",
            "sdirk-eight-silent-one-seven-six-shared",
            "sdirk-eight-silent-one-seven-distinct-anchors",
            "sdirk-eight-silent-one-seven-distinct-coprime",
            "sdirk-eight-silent-one-seven-distinct-one-front-zero",
            "sdirk-eight-silent-one-seven-distinct-literal-pole"):
    sys.path.insert(0,str(root/dep))
from itertools import product
from sympy import isprime
from constant_literal_reverse import ctest,cshared
from gauss_literal_reverse import verify

def main():
    p,t=1103,161
    assert isprime(p) and (2*t*t-1)%p==0
    n=m=l=0
    for f,i,k in product((True,False),(0,1),(True,False,None)):
        assert verify(f,i,k);n+=1
        assert cshared(f,i,k,p,t);l+=1
        if k is not None:
            assert ctest(f,i,k,p,t);m+=1
    assert (n,m,l)==(12,8,12)
    print('literal reverse-root checks:',n,m,l)

if __name__=='__main__':main()
