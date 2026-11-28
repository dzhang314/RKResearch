"""Both independent arithmetic-front star-rear B≠0 literal 2/3 closures.

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
    "sdirk-eight-silent-one-eight-reverse-live-arithmetic-star4-regular-closed",
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

from arith_literal_diagonal import norm_factors,reconstruct,mod_images,int_input
from arith_literal_fibers import E,ExField,all_mod,guards,sc,trim,fast_orientation,fast_guard
from regular_star_projection import raw

# Whole norm factors and their complete place counts.
DIRECT={
    (336,1):{'orientation':6,'fifth':4},
    (22,3):{'orientation':3,'fifth':3},
}
# Exact oriented degree, actual guard, exact fourth degree removed,
# no-fourth-root residue count for silence at physical 2 and 3 respectively.
PLAN={
    (34,3):(17,'scale',3,(2,3)),
    (2,6):(1,'terminal_literal',0,(0,0)),
    (6,6):(3,'B',1,(1,1)),
    (22,6):(11,'rear_literal',3,(2,1)),
    (54,6):(27,'terminal_h',3,(3,3)),
    (42,24):(21,'nodal_lead',3,(3,3)),
    (16,24):(8,'nodal_lead',6,(2,2)),
}

def check_place(slot,p,t):
    P,Q,*_=raw(False,slot)
    assert (P.degrees()[1:3],Q.degrees()[1:3])==((9,29),(26,79))
    U,V=map(int_input,(P,Q))
    assert (U[2]**26*V[2]**9).bit_length()=={2:5266,3:5269}[slot]
    W=mod_images(U[:2],V[:2],p,2*t,1465,(9,26))
    assert any(v[-1] for v in W)
    A,B=reconstruct(slot)
    assert max(A.degree(),B.degree())==1200

def check_slot(slot):
    p,t=1129,203
    assert isprime(p) and (2*t*t-1)%p==0
    check_place(slot,p,t)
    factors=norm_factors(slot)
    assert sorted((M.degree(),e) for M,e in factors)==sorted(DIRECT.keys()|PLAN.keys())
    ans=Counter();whole=0
    for R,e in factors:
        d,e=R.degree(),e
        W=fmpq_poly(R);M=E(W*(1/W[W.degree()]))
        if (d,e) in DIRECT:
            ok,tally,bad,_=all_mod(slot,M,p,t)
            assert ok and not bad and tally==DIRECT[d,e]
            ans.update(tally)
            continue
        deg,name,n,counts=PLAN[d,e]
        M=fast_orientation(M,deg,slot)
        assert M.degree()==deg and M.lc()==E(1)
        K=ExField(M)
        PF,GG,SS=guards(slot)
        suffix='a' if slot==2 else 'b'
        if name=='terminal_literal':
            assert not K(dict(GG)['terminal_'+suffix])
            assert n==0 and counts==(0,0)
            whole+=1
            print("exact entire diagonal collides with actual terminal",slot,deg,flush=True)
            continue
        if name=='rear_literal':
            name='rear_'+suffix
        P0=trim(list(map(K,PF[0])))
        S=trim(list(map(K,{k:v for k,v,_ in SS}[name])))
        assert P0 and S
        X=fast_guard(K,P0,S,n,name)
        U=sc(X,X[-1].inv())
        ok,tally,bad,_=all_mod(slot,M,p,t,U)
        assert ok and not bad and tally=={'no_s':counts[slot-2]}
        ans.update(tally)
    assert whole==1 and ans=={'no_s':13,'orientation':9,'fifth':7}
    print("actual silent literal complete",slot,dict(ans),whole,flush=True)

def main():
    for slot in (2,3):
        check_slot(slot)
    print("both arithmetic-front star-rear nonzero literal placements excluded",flush=True)

if __name__=="__main__":
    main()
