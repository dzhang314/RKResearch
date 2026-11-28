"""Exact arithmetic-front/star-rear nonzero centered coefficient closure.

Pinned arithmetic dependencies: sympy==1.14.0, python-flint==0.9.0.
"""
from pathlib import Path
from collections import Counter
from sympy import isprime
from flint import fmpq_poly
import sys

ROOT=Path(__file__).resolve().parent.parent
DEPS=(
    "sdirk-eight-half-quadratic",
    "sdirk-eight-half-star-quadratic",
    "sdirk-eight-silent-one-eight-reverse-live-constant",
    "sdirk-eight-silent-one-eight-reverse-live-regular-finite",
    "sdirk-eight-silent-one-eight-reverse-live-star4-regular-closed",
    "sdirk-eight-silent-one-seven-distinct-anchors",
    "sdirk-eight-silent-one-seven-distinct-coprime",
    "sdirk-eight-silent-one-seven-six-anchored",
    "sdirk-eight-silent-one-seven-six-reverse",
    "sdirk-eight-silent-one-seven-six-shared",
    "sdirk-eight-silent-three-closure",
    "sdirk-eight-silent-two-equal",
    "sdirk-eight-silent-two-high",
    "sdirk-eight-silent-two-unequal",
)
for dep in DEPS:
    sys.path.append(str(ROOT/dep))

from arith_star_diagonal import norm_factors
from arith_star_fibers import E,ExField,all_mod,guards,sc,trim
from paired_proposals import fast_orientation,fast_guard

# Norm factor: exact orientation degree, real guard, divided fourth degree,
# total reduced components of that monic orientation after exclusion.
PLAN={
    (24,1):(12,"nodal_lead",1,8),
    (522,1):(None,None,0,8),
    (6,3):(3,"quintic",1,1),
    (16,6):(8,"B",3,2),
    (42,8):(21,"nodal_lead",2,3),
    (8,10):(4,"nodal_lead",2,1),
}

def main():
    p,t=1129,203
    assert isprime(p) and (2*t*t-1)%p==0
    factors=norm_factors()
    assert sorted((M.degree(),e) for M,e in factors)==sorted(PLAN)
    total=Counter()
    for R,e in factors:
        d,nm,n,c=PLAN[R.degree(),e]
        M=fmpq_poly(R)
        U=E(M*(1/M[M.degree()]))
        if d is None:
            ok,tally,bad=all_mod(U,p,t)
            assert tally=={"orientation":7,"both_fifths":1}
        else:
            Q=fast_orientation(U,d)
            assert Q.degree()==d and Q.lc()==E(1)
            K=ExField(Q)
            P0,G=guards()
            P0=trim(list(map(K,P0)))
            J=trim(list(map(K,G[nm])))
            assert P0 and J
            F=fast_guard(K,P0,J,n,nm)
            S=sc(F,F[-1].inv())
            ok,tally,bad=all_mod(Q,p,t,S)
            assert tally=={"no_s":c}
        assert ok and not bad and sum(tally.values())==c
        total.update(tally)
    assert total=={"no_s":15,"orientation":7,"both_fifths":1}
    print("arithmetic front/star rear actual silent 5/6/7 nonzero coefficient excluded",
          dict(total),flush=True)

if __name__=="__main__":
    main()
