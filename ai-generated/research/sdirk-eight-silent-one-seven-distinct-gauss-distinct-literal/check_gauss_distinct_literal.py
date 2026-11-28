"""Verify the distinct-root Gauss chart at a literal silent clock."""
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
            "sdirk-eight-silent-one-seven-distinct-gauss-root"):
    sys.path.insert(0,str(root/dep))
from itertools import product
from sympy import isprime
from gauss_distinct_literal import phase2

def main():
    p,t=1129,203
    assert isprime(p) and (2*t*t-1)%p==0
    A=B=C=0
    for f,i,m in product((True,False),(0,1),(True,False,None)):
        assert phase2(f,i,m,'shared',p,t);C+=1
        if m is not None:
            assert phase2(f,i,m,'sole',p,t);A+=1
            assert phase2(f,i,m,'neither',p,t);B+=1
    assert (A,B,C)==(8,8,12)
    print('different Gauss literal reverse-root checks:',A,B,C)

if __name__=='__main__':main()
