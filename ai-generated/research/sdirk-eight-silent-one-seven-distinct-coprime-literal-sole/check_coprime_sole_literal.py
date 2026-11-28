"""Replay coprime affine denominators pinned by one active and one sole literal."""
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
            "sdirk-eight-silent-one-seven-distinct-literal-pole"):
    sys.path.insert(0,str(root/dep))
from itertools import product
from sympy import isprime
from coprime_sole_literal import case

def main():
    p,t=1103,161
    assert isprime(p) and (2*t*t-1)%p==0
    n=0
    for f,i,j in product((True,False),(0,1),(True,False)):
        assert case(f,i,j,p,t);n+=1
    assert n==8
    print('coprime sole-literal reverse-root checks:',n)

if __name__=='__main__':main()
