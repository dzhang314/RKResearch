"""Replay the nonliteral constant-Q strict SDIRK8 chart."""
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
            "sdirk-eight-silent-one-seven-distinct-literal-pole",
            "sdirk-eight-silent-one-seven-distinct-literal-reverse",
            "sdirk-eight-silent-one-seven-distinct-gauss-root",
            "sdirk-eight-silent-one-seven-distinct-gauss-nonliteral"):
    sys.path.insert(0,str(root/dep))
from itertools import product
from sympy import isprime
from constant_front_tail import one

def main():
    p,t=1103,161
    assert isprime(p) and (2*t*t-1)%p==0
    n=0
    for f,i,j in product((True,False),(0,1),('star','arith','silent')):
        assert one(f,i,j,p,t);n+=1
    assert n==12
    print('constant nonliteral reverse-root checks:',n)

if __name__=='__main__':main()
