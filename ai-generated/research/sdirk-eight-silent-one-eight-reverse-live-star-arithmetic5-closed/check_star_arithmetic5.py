"""Complete actual reverse-live physical fifth in its regular star/arithmetic chart."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent.parent
for dep in (
    "sdirk-eight-half-quadratic",
    "sdirk-eight-half-star-quadratic",
    "sdirk-eight-silent-one-eight-reverse-live-constant",
    "sdirk-eight-silent-one-eight-reverse-live-exceptional",
    "sdirk-eight-silent-one-eight-reverse-live-regular-finite",
    "sdirk-eight-silent-one-eight-reverse-live-regular-silent-eighth-finite",
    "sdirk-eight-silent-one-eight-reverse-live-star4-regular-closed",
    "sdirk-eight-silent-one-eight-reverse-live-star-silent-eighth-closed",
    "sdirk-eight-silent-one-eight-reverse-live-arithmetic-star567-regular-closed",
    "sdirk-eight-silent-one-eight-reverse-live-arithmetic-silent-eighth-closed",
    "sdirk-eight-silent-one-eight-reverse-live-star-arithmetic67-closed",
    "sdirk-eight-silent-one-seven-distinct-anchors",
    "sdirk-eight-silent-one-seven-distinct-coprime",
    "sdirk-eight-silent-one-seven-six-anchored",
    "sdirk-eight-silent-one-seven-six-reverse",
    "sdirk-eight-silent-one-seven-six-shared",
    "sdirk-eight-silent-three-closure",
    "sdirk-eight-silent-two-equal",
    "sdirk-eight-silent-two-high",
    "sdirk-eight-silent-two-unequal",
):
    sys.path.append(str(ROOT/dep))

from rear5_diagonal import diagonal,cover,PLAN
from rear5_model import model5
from check_star_arithmetic67 import (gfiber, s_coeffs, mono, pol_mod,
     exact_support)
from flint import fmpq_poly,nmod_poly
from star4_guarded_fibers import Field,gpoly,modQ
from star4_actual_fifth import Bfield,gcdp,sc,trim
from regular_star_projection import Co
from silent8_fibers import sfactors,getpoly
from ordinary_reconstruction import extend
from sympy import isprime

def assert_no_actual_tail(L,gg,S,p,t):
    A,B,D=model5()
    U,s,inc=extend(L,S);g=inc(gg)
    V=[getpoly(D[key],U,g,s,p,t) for key in ('N','S','F','Gsilent')]
    assert len(V[0])==5
    W=mono(V[0])
    for P in V[1:]:W=gcdp(W,P)
    assert len(W)==1

def checked_fibers(M,p,t,kind=None):
    A,B,D=model5()
    K=Field(fmpq_poly(M));base=None
    if kind is not None:
        e,s0,guard,n,count=PLAN[kind]
        P,Q=(trim([K(fmpq_poly(L)) for L in s_coeffs(F)]) for F in (A,B))
        base=mono(min((F for F in (P,Q) if F),key=len))
        assert len(base)==s0+1
        if n:
            G=trim([K(gpoly(f)) for f in Co(D['guards'][guard],1)])
            base=exact_support(base,G,K,n)
        assert len(base)==s0+1-n
    G=modQ(K.M,p)
    assert G.degree()==M.degree() and G.leading_coefficient()==1
    product=nmod_poly([1],p);total=0
    for R,e in G.factor()[1]:
        product*=R**e;L=Bfield(R,p,t);gg=L(nmod_poly([0,1],p))
        P,Q=(gfiber(F,L) for F in (A,B))
        if base is not None:
            W=pol_mod(base,L,p)
            assert len(base)==len(W) and W[-1]==1
            assert len(gcdp(gcdp(W,P),Q))==1
        else:
            assert len(P)==49 or len(Q)==55
            W=gcdp(P,Q)
            assert len(W)>1
            F=sfactors(W,L)
            assert len(F)==1
            for T,k in F:assert_no_actual_tail(L,gg,T,p,t)
        total+=1
    assert product==G
    return total

def verify_diagonal(D):
    Q,C=cover(D)
    p,t=65537,2040
    assert isprime(p) and (2*t*t-1)%p==0
    common=checked_fibers(Q,p,t);assert common==12
    other=0
    for key,M in C.items():
        n=checked_fibers(M,p,t,key)
        assert n==PLAN[key][-1]
        other+=n
        print('all exact guarded fourth components',key,n,flush=True)
    assert other==39
    print('excluded actual silent fifth, regular star/ordinary-arithmetic',
          {'complete_true_tail_and_silent_fifth':common,'complete_guarded_fourths':other},flush=True)

if __name__=='__main__':verify_diagonal(diagonal())
