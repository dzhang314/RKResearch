"""Complete regular arithmetic-front constant numerator with actual silent eighth.

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
    "sdirk-eight-silent-one-eight-reverse-live-exceptional",
    "sdirk-eight-silent-one-eight-reverse-live-regular-finite",
    "sdirk-eight-silent-one-eight-reverse-live-regular-silent-eighth-finite",
    "sdirk-eight-silent-one-eight-reverse-live-star4-regular-closed",
    "sdirk-eight-silent-one-eight-reverse-live-star-silent-eighth-closed",
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

from exact_product_cover import verified_cover
from arith_silent8_fibers import E,ExField,all_mod,guards,orientation_for,fast_guard,sc,trim

# Product cover factor degree and exponent: switched orientation degree,
# exact true-pivot support removed, complete no-fourth-root components.
PLAN={
    (48,1):(24,1,6),
    (18,8):(9,4,3),
    (60,12):(30,4,2),
    (24,15):(12,5,8),
    (42,42):(21,7,3),
    (4,72):(4,12,4),
    (8,102):(4,10,1),
}

def main():
    p,t=1129,203
    assert isprime(p) and (2*t*t-1)%p==0
    F=verified_cover()
    assert sorted((M.degree(),e) for M,e in F)==sorted({(5108,1),*PLAN})
    total=Counter()
    for R,e in F:
        d=R.degree()
        W=fmpq_poly(R); M=E(W*(1/W[d]))
        if d==5108:
            ok,done,bad,_=all_mod(M,p,t)
            assert done=={'orientation':19,'no_distinct_fifth':5,'arith_chronology':6}
        else:
            n0,n,c=PLAN[d,e]
            S=M if n0==d else orientation_for(M,n0)
            assert S.degree()==n0 and S.lc()==E(1)
            K=ExField(S)
            P0,_,H=guards()
            P=trim(list(map(K,P0[0])))
            G=trim(list(map(K,{k:u for k,u,_ in H}['nodal_lead'])))
            assert P and G
            J=fast_guard(K,P,G,n,'nodal_lead')
            U=sc(J,J[-1].inv())
            ok,done,bad,_=all_mod(S,p,t,U)
            assert done=={'no_s':c}
        assert ok and not bad
        total.update(done)
    assert total=={'orientation':19,'no_distinct_fifth':5,'arith_chronology':6,'no_s':27}
    print("regular arithmetic-front constant numerator with actual silent eighth excluded",
          dict(total),flush=True)

if __name__=="__main__":
    main()
