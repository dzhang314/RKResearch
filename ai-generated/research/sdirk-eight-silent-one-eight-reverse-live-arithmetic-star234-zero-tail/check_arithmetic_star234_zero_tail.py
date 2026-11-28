"""Arithmetic-front/star-rear A=B=0 at actual silent 2, 3, or 4."""
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parent.parent
DEPS=(
    "sdirk-eight-half-quadratic",
    "sdirk-eight-half-star-quadratic",
    "sdirk-eight-silent-one-eight-reverse-live-constant",
    "sdirk-eight-silent-one-eight-reverse-live-regular-finite",
    "sdirk-eight-silent-one-eight-reverse-live-star4-zero-tail",
    "sdirk-eight-silent-one-eight-reverse-live-star4-regular-closed",
    "sdirk-eight-silent-one-eight-reverse-live-arithmetic-star567-zero-tail",
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

from check_arithmetic_star567_zero_tail import exact_data
from zero_tail_rank import (
    Bfield,Tower,Nested,nmod_poly,sc,qr,add,mul,ev,nodal,det,ccols,
)
from regular_star_projection import Co
from star4_actual_fifth import lv
from seven_k0_anchors import h4,pol,cv
from math import comb
from sympy import isprime

def test(p,t,verbose=True):
    J,HH,base=exact_data()
    U=Bfield(nmod_poly([0,1],p),p,t)
    D=nmod_poly([int(lv(G,U,U(0),U(0),p,t).x[0]) for G in Co(J,2)],p)
    if D.degree()!=8:raise ArithmeticError('diagonal leading')
    summary=[]
    for M,e in D.factor()[1]:
        K=Bfield(M,p,t);g=K(nmod_poly([0,1],p));g.inv()
        get=lambda F:lv(F,K,g,K(0),p,t)
        a,b,mo,ha,hb=map(get,base);H=list(map(get,HH))
        H=sc(H,ha/ev(H,g*a));assert ev(H,g*b)==hb
        H4=[cv(K,c) for c in pol(h4(False),lambda x:x)]
        S,R=qr(add([c*g**j for j,c in enumerate(H)],sc(H4,-1)),nodal([a,b]))
        assert not R and len(S)<=4
        if len(S)!=4:raise ArithmeticError('fourth leading')
        U=Tower(sc(S,S[-1].inv()));s=U.gen();g,a,b=map(U,(g,a,b))
        root=[g*a,g*b,g*s];x=1-g;m=1-2*g
        H=list(map(U,H));Hx=ev(H,x)
        h=[sum((H[i]*comb(i,j)*m**(i-j)*g**j for i in range(j,6)),U(0)) for j in range(6)]
        assert not h[4]+h[5] and not h[2]+h[3]+Hx
        for j,z in enumerate(root):
            DQ=[(x-z)*h[0]-2*(m-z)*Hx,(x-z)*h[2]+(m-z)*Hx,(x-z)*h[4]]
            V=Nested(sc(DQ,DQ[-1].inv()));w=V.gen()
            g0=V(g);m0=V(m)
            pegs=[V(o) for i,o in enumerate(root) if i!=j]+[V(x)]
            E=mul(nodal(pegs),[m0*m0-g0*g0*w,-2*m0,V(1)])
            P=list(map(V,H))
            det(ccols(E,P,V)).inv()
            summary.append((M.degree(),e,j+2))
            if verbose:print('literal rank zero',p,t,M.degree(),e,j+2,flush=True)
    return sorted(summary)

def main():
    p,t=1129,203
    assert isprime(p) and (2*t*t-1)%p==0
    assert test(p,t)==[(d,1,j) for d in (1,7) for j in (2,3,4)]
    print("arithmetic front/star rear, literal silent 2/3/4, zero tail excluded",flush=True)

if __name__=="__main__":
    main()
