"""Replay all one-front distinct nonliteral Gauss reverse-root placements."""
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
from gauss_small_nonliteral import star_check
from exact_hole8_h4 import verify
from front_tail_close import diag

def main():
    normal,switched=(1129,203),(1559,529)
    for p,t in (normal,switched):
        assert isprime(p) and (2*t*t-1)%p==0
    A=B=C=0
    for f,i in product((True,False),(0,1)):
        assert star_check(f,i,*normal);A+=1
        assert verify(f,i,*normal);B+=1
        for typ,mode in product(('ord','hole'),('arith','silent')):
            sp=(switched if i==0 and typ=='ord' and (not f or mode=='arith') else normal)
            assert diag(f,i,typ,mode,*sp);C+=1
    assert (A,B,C)==(4,4,16)
    print('Gauss distinct nonliteral reverse-root checks:',A,B,C)

if __name__=='__main__':main()
