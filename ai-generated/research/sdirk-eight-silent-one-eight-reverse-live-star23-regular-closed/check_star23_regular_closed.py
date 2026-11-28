"""Complete two-literal exchange and constant-numerator star/rear proof."""
from pathlib import Path
from sympy import isprime
import sys
root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic", "sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-one-eight-reverse-live-constant",
            "sdirk-eight-silent-one-eight-reverse-live-regular-finite",
            "sdirk-eight-silent-one-eight-reverse-live-star4-zero-tail",
            "sdirk-eight-silent-one-eight-reverse-live-star4-regular-closed",
            "sdirk-eight-silent-one-seven-distinct-anchors",
            "sdirk-eight-silent-one-seven-distinct-coprime",
            "sdirk-eight-silent-one-seven-six-anchored",
            "sdirk-eight-silent-one-seven-six-reverse",
            "sdirk-eight-silent-one-seven-six-shared",
            "sdirk-eight-silent-three-closure", "sdirk-eight-silent-two-equal",
            "sdirk-eight-silent-two-high", "sdirk-eight-silent-two-unequal"):
    sys.path.append(str(root/dep))
from regular_star_projection import raw,con,profile
from seven_k0_anchors import ends,F2,cv
from lateral_diagonal import exact_factors
from lateral_fibers import PLAN,one_factor
from zero_tail_lateral import ex_constants,test

def main():
    p,t=1129,203
    assert isprime(p) and (2*t*t-1)%p==0
    A,B,m=[cv(F2,w) for w in ends(True,1)]
    assert not m
    L,R=[raw(True,slot)[:4] for slot in (2,3)]
    assert tuple(map(con,L))==tuple(R)
    h,P,V,D,_=profile(True)
    assert all(con(z)==z for z in h) and all(con(z)==-z for z in (P,V,D))
    ex_constants()
    for slot in (2,3):
        assert test(slot,p,t)==3
    J,factors=exact_factors()
    assert sorted((M.degree(),e) for M,e in factors)==sorted(PLAN)
    for M,e in factors:
        one_factor(J,M,e,p,t)
        print('complete lateral norm factor excluded',M.degree(),e,flush=True)
    print('all regular literal silent-two and silent-three star-star factors excluded',flush=True)

if __name__=='__main__':
    main()
