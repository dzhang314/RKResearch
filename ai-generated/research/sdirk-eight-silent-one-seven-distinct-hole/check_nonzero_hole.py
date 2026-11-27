"""Check the fixed Gauss-hole diagonal and every actual terminal placement."""
from pathlib import Path
import sys
root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic","sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-three-closure","sdirk-eight-silent-two-unequal",
            "sdirk-eight-silent-two-equal","sdirk-eight-silent-two-high",
            "sdirk-eight-silent-one-seven-six-anchored",
            "sdirk-eight-silent-one-seven-six-reverse"):
    sys.path.insert(0,str(root/dep))
from sympy import isprime
from hole_nonzero import exact_factors,special,standard

def main():
    p,t=1103,161
    assert isprime(p) and (2*t*t-1)%p==0
    n=0
    for f in (True,False):
        M=exact_factors(f)
        assert [X.degree() for X in M]==[12]
        for rear in (None,True,False):
            for hit in ((0,9) if rear is None else (0,8,9)):
                assert (special(f,M[0],rear,hit,p,t) if hit else standard(f,M[0],rear,p,t))
                n+=1
    assert n==16
    print('nonzero-factor both-front Gauss-hole orientations excluded:',n)
if __name__=='__main__':main()
