"""Check the finite-profile gate, not an exclusion, for both literal fronts silent."""
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
            "sdirk-eight-silent-one-seven-distinct-gauss-nonliteral",
            "sdirk-eight-silent-one-seven-distinct-constant-nonliteral",
            "sdirk-eight-silent-one-seven-distinct-coprime-shared-eighth",
            "sdirk-eight-silent-one-seven-distinct-coprime-shared-star",
            "sdirk-eight-silent-one-seven-distinct-coprime-shared-arithmetic"):
    sys.path.insert(0,str(root/dep))
from itertools import product
from sympy import isprime
from nofront_arith_finite_gate import verify
from nofront_arith_tails import guards

def main():
    for p,t in ((1103,161),(1129,203),(1559,529)):
        assert isprime(p) and (2*t*t-1)%p==0
    n=0
    for f,i in product((True,False),(0,1)):
        assert len(guards(f,i))==2
        assert verify(f,i);n+=1
    assert n==4
    print('no-active-literal arithmetic finite-profile checks:',n)

if __name__=='__main__':main()
