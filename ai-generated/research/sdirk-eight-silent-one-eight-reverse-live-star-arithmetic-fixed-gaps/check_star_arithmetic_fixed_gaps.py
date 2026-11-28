"""Regular star-front ordinary-arithmetic-rear nonliteral fixed gaps, exactly."""
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

from regular_silent_eighth import silent8_system
from regular_star_projection import Co,ev,front_projection,g,left,profile,red
from check_star_family import F
from quadratic_poly import E
from star4_actual_fifth import gcdp,qr,trim
from flint import fmpq_mpoly_ctx,fmpq_poly
Q=fmpq_mpoly_ctx.get(['g','s'])

def arr(P):
    T={}
    for (i,j,k,l),w in P.to_dict().items():
        assert i==l==0              # star-front literal swap is symmetric
        T[k,j]=w
    return Q.from_dict(T)

def diagonal(P):
    T={}
    for (i,j),w in P.to_dict().items():
        assert not j
        T[i]=w
    return fmpq_poly([T.get(i,0) for i in range(max(T,default=-1)+1)])

def peel(P,F):
    assert F.degree()>0
    while P:
        D,R=divmod(P,F)
        if R:break
        P=D
    return P

def monic(P):
    assert P
    return P*(1/P[P.degree()])

def main():
    _,_,N,*_=silent8_system(True)
    R=Co(N)
    H,_,_,_,(a,b,q,La,Lb,_,_)=profile(True)
    _,_,exc=map(left,front_projection(True))
    M=monic(diagonal(arr(exc)))
    assert M.degree()==21
    K=F(E(M))
    def fourth(P):
        return trim([K(E(diagonal(arr(C)))) for C in Co(P,1)])
    G=fourth(R[4])
    x=1-g
    for u in (1,2):
        k=1+2*u-u*u; h=-2+u+4*u*u-u**3; j=2+3*u-12*u*u+4*u**3
        c=x-g*u;d=x-2*g*u
        T=red(h*ev(H,d)+2*j*ev(H,c)-k*j*ev(H,x))
        # Pure strict-diagonal guards: nonzero gamma, two early L4 values,
        # and the three actual rear clocks distinct from both literal fronts.
        gguards=list(map(lambda Z:diagonal(arr(Z)),(
            g,red(La*Lb),red((x-a)*(x-b)),
            red((c-a)*(c-b)),red((d-a)*(d-b)))))
        R1,R2=ev(R,u),ev(R,2*u)
        D1=diagonal(arr(R1).resultant(arr(R2),1))
        D2=diagonal(arr(R1).resultant(arr(T),1))
        assert D1 and D2
        for F0 in gguards:
            D1=peel(D1,F0)
            D2=peel(D2,F0)
        C=monic(D1.gcd(D2))
        assert C==M*M
        print('fixed gap exact diagonal support',u,C.degree(),M.degree(),flush=True)

        # Exact Euclidean identities in the monic diagonal algebra. The
        # inverse routine verifies units; the argument does not need M prime.
        U=gcdp(fourth(R1),fourth(R2));assert len(U)==3
        U=gcdp(U,fourth(T));assert len(U)==2 and U[-1]==1
        _,rr=qr(G,U);assert not rr
        print('fixed gap excluded by exact true quartet pivot',u,flush=True)

if __name__=='__main__':
    main()
