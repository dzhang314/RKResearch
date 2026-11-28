"""Exact neither-front exclusion for the seven-distinct zero-factor chart."""
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
            "sdirk-eight-silent-one-seven-distinct-one-front-zero"):
    sys.path.insert(0,str(root/dep))
from itertools import product
from sympy import isprime
from no_front_zero import verify

def main():
    p,t=1103,161
    assert isprime(p) and (2*t*t-1)%p==0
    n=0
    for f,slot,rear,ori in product((True,False),(0,1),(True,False),(1,-1)):
        assert verify(f,slot,rear,ori,p,t)
        n+=1
    assert n==16
    print('neither-front seven-distinct zero-factor checks:',n)
if __name__=='__main__':main()
