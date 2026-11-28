"""Exact regular arithmetic-front star-rear, physical silent fourth, B nonzero.

Arithmetic dependencies: sympy==1.14.0, python-flint==0.9.0.
"""
from pathlib import Path
from collections import Counter
from flint import fmpq_poly
from sympy import isprime
import sys

ROOT=Path(__file__).resolve().parent.parent
DEPS=(
    "sdirk-eight-half-quadratic",
    "sdirk-eight-half-star-quadratic",
    "sdirk-eight-silent-one-eight-reverse-live-constant",
    "sdirk-eight-silent-one-eight-reverse-live-regular-finite",
    "sdirk-eight-silent-one-eight-reverse-live-star4-regular-closed",
    "sdirk-eight-silent-one-eight-reverse-live-arithmetic-star567-regular-closed",
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

from arith_literal_diagonal import norm_factors
from arith_literal_fibers import E,ExField,all_mod,guards,sc,trim,fast_orientation,fast_guard

# Exact oriented degree, actual guard, its fourth degree removed, full residue counts.
PLAN={
    (272,1):(None,None,0,{'orientation':8,'fifth':5}),
    (78,1):(39,'scale',1,{'no_s':5}),
    (90,2):(45,'scale',1,{'no_s':5}),
    (18,2):(9,'terminal_q',1,{'no_s':3}),
    (22,3):(None,None,0,{'orientation':3,'fifth':3}),
    (54,6):(27,'terminal_h',3,{'no_s':3}),
    (6,8):(3,'quintic',1,{'no_s':1}),
    (42,24):(21,'nodal_lead',3,{'no_s':3}),
    (16,24):(8,'nodal_lead',6,{'no_s':2}),
}

def main():
    p,t=1129,203
    assert isprime(p) and (2*t*t-1)%p==0
    F=norm_factors(4)
    assert sorted((M.degree(),e) for M,e in F)==sorted(PLAN)
    total=Counter()
    for R,e in F:
        d,nm,n,c=PLAN[R.degree(),e]
        W=fmpq_poly(R); M=E(W*(1/W[W.degree()]))
        if d is None:
            ok,tally,bad,_=all_mod(4,M,p,t)
        else:
            M=fast_orientation(M,d,4)
            assert M.degree()==d and M.lc()==E(1)
            K=ExField(M)
            P0,_,L=guards(4)
            P=trim(list(map(K,P0[0])))
            S=trim(list(map(K,{k:v for k,v,_ in L}[nm])))
            assert P and S
            X=fast_guard(K,P,S,n,nm)
            U=sc(X,X[-1].inv())
            ok,tally,bad,_=all_mod(4,M,p,t,U)
        assert ok and not bad and tally==c
        total.update(tally)
    assert total=={'no_s':22,'orientation':11,'fifth':8}
    print("actual arithmetic-front star-rear physical fourth, nonzero tail excluded",
          dict(total),flush=True)

if __name__=="__main__":
    main()
