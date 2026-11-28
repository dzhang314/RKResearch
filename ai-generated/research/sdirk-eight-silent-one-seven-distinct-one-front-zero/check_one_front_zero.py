"""Exact verification of the single-active-front seven-clock zero-factor chart."""
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
            "sdirk-eight-silent-one-seven-distinct-coprime"):
    sys.path.insert(0,str(root/dep))
from itertools import product
from sympy import isprime
from literal_terminal import only_literal,both_literal
from off_literal_active8 import verify_active
from off_literal_silent8 import verify_silent

def main():
    p,t=1103,161
    assert isprime(p) and (2*t*t-1)%p==0
    A=B=C=0
    for f,i,j,e in product((True,False),(0,1),(None,True,False),(1,-1)):
        assert both_literal(f,i,j,e,p,t);A+=1
        if j is not None:
            assert only_literal(f,i,j,e,p,t);A+=1
            for q4 in (True,False):
                assert verify_active(f,i,j,e,q4,p,t);B+=1
        else:
            assert verify_silent(f,i,e,p,t);C+=1
    assert (A,B,C)==(40,32,8)
    print('one-front zero-factor seven-distinct checks:',A,B,C)
if __name__=='__main__':main()
