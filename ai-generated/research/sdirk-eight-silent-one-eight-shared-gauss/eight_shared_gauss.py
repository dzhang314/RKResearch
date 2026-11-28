"""Eight distinct active clocks with reverse-silent fourth and shared Gauss root."""
from pathlib import Path
import sys
from itertools import product
from sympy import isprime
root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic", "sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-one-seven-distinct-coprime",
            "sdirk-eight-silent-one-seven-distinct-hole",
            "sdirk-eight-silent-one-seven-six-anchored",
            "sdirk-eight-silent-one-seven-six-reverse",
            "sdirk-eight-silent-one-seven-six-shared",
            "sdirk-eight-silent-three-closure", "sdirk-eight-silent-two-equal",
            "sdirk-eight-silent-two-high", "sdirk-eight-silent-two-unequal"):
    sys.path.append(str(root/dep))
from extra_active import invpoly
from hole_nonzero import exact_factors
from both_front_silent8 import *
from arithmetic_nonzero import guarded
from off8_fibers import det,cramer,multicol

@lru_cache(None)
def exact_gap(front,M,rear):
    K,g,X,R,A,B,m,ha,hb,L,Q,P,H4=model(front,M)
    XminusR=X-R
    assert XminusR and A!=R and B!=R and g and Q[1]
    u=[K(0),K(1)]; k=[K(1),K(2),K(-1)]
    c=[X,K(-1)]
    d=[X-K(2),K(1)] if rear else [X,K(-2)]
    pc,pd,px=subst(P,c),subst(P,d),ev(P,X)
    H=[K(-2),K(1),K(4),K(-1)]; J=[K(2),K(3),K(-12),K(4)]
    if rear:
        F=sum_poly([mul([K(2),K(-1)],pc),sc(mul(u,pd),-1),
                    sc(mul(k,[K(-2),K(2)]),px)])
    else:
        assert ev(J,XminusR/2)
        F=sum_poly([sc(mul(J,pc),2),mul(H,pd),sc(mul(k,J),-px)])
    pegs=[[A],[B],[X],c,d,[R]]
    guards=[u,k]
    for i in range(len(pegs)):
        for j in range(i):
            dd=add(pegs[i],sc(pegs[j],-1)); assert dd
            guards.append(dd)
    assert F
    gap=mon(guarded(F,guards))
    print('shared Gauss exact gap',front,M.degree(),rear,len(gap)-1,flush=True)
    return gap,(g,X,R,A,B,m,ha,hb,P,H4)

def direct_hole(front,M,p,t):
    K,g,X,R,A,B,m,ha,hb,L,Q,P,H4=model(front,M)
    s=(X-R)/2
    J=4*s**3-12*s**2+3*s+2
    assert J
    E=first5(K,A,B,m,ha,hb,[],list(H4))
    fifth=ev(E,R)
    assert fifth
    for U,u in reduced(M,p,t,[-s,K(1)]):
        U(J).inv()
        U(fifth).inv()

def finite(front,M,rear,p,t):
    un,ds=exact_gap(front,M,rear)
    if len(un)<=1:
        return 0
    count=0
    for K,u in reduced(M,p,t,un):
        g,X,R,A,B,m,ha,hb=map(K,ds[:8])
        P,H4=[list(map(K,V)) for V in ds[8:]]
        c=X-u; d=X-(2-u if rear else 2*u); k=1+2*u-u*u
        r=g*R; x=g*X
        g.inv(); k.inv()
        pegs=[g*A,g*B,x,g*c,g*d]
        all_sites=pegs+[r]
        for i,j in product(range(6),repeat=2):
            if i>j:
                (all_sites[i]-all_sites[j]).inv()
        L=mon(list(map(K,Lco)))
        U,rem=qr(L,[-r,K(1)])
        assert not rem and len(U)==4 and U[-1]==K(1)
        nu=intp(K,U)/ev(U,r)
        W=[sum(U[j]*(K(1)/(j-i)-nu*r**(j-i-1))
               for j in range(i+1,4)) for i in range(3)]
        px,pc=ev(U,x),ev(U,g*c)
        rho=[-g*c*k*px+x*pc,k*px-pc]
        V=sc(qr(mul(rho,invpoly(K,W,U)),U)[1],-1)
        rows=[[ev(U,y)*y**j for j in range(4)]+[ev(V,y)] for y in pegs]
        rhs=[-ev(U,y)*y**4 for y in pegs]
        di=det(rows).inv()
        u0,u1,u2,u3,lam=[v*di for v in cramer(rows,rhs)]
        D=add(mul(U,[u0,u1,u2,u3,K(1)]),sc(V,lam))
        W,rem=qr(D,nodal(pegs))
        assert not rem and len(W)==3 and W[-1]==K(1)
        assert len(D)==8 and D[-1]==K(1)
        Y=[v*g**(i-2) for i,v in enumerate(W)]
        E=first5(K,A,B,m,ha,hb,P,H4)
        multicol(Y,E).inv()
        count+=1
    print('shared Gauss fifth units',front,rear,count,flush=True)
    return count

if __name__=='__main__':
    p,t=1103,161
    assert isprime(p) and (2*t*t-1)%p==0
    for f in (True,False):
        Ms=exact_factors(f)
        assert [M.degree() for M in Ms]==[12]
        for M in Ms:
            direct_hole(f,M,p,t)
            for rear in (True,False):
                finite(f,M,rear,p,t)
    print('all four scoped shared-Gauss-numerator phases excluded',flush=True)
