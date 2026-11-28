"""Exact diagonal, literal trailing ratio, and active fifth gate at T constant."""
from pathlib import Path
import sys
from itertools import product
from sympy import isprime

root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic", "sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-one-seven-distinct-anchors",
            "sdirk-eight-silent-one-seven-distinct-coprime",
            "sdirk-eight-silent-one-seven-six-anchored",
            "sdirk-eight-silent-one-seven-six-reverse",
            "sdirk-eight-silent-one-seven-six-shared",
            "sdirk-eight-silent-three-closure", "sdirk-eight-silent-two-equal",
            "sdirk-eight-silent-two-high", "sdirk-eight-silent-two-unequal"):
    sys.path.append(str(root/dep))

from extra_active import invpoly
from seven_k0_anchors import *
from constant_q_nonzero import gamma_factors

@lru_cache(None)
def exact_gap(front,M,rear):
    K=ExField(Epoly(M)); gamma=K(E(P([0,1])))
    A,B,m=(cv(K,q) for q in ends(front,1))
    ha,hb=(A-1)/2,(B-1-m)/2
    L=list(map(K,Lco)); q=ev(L,gamma*A)/ha
    assert gamma and q and q==ev(L,gamma*B)/hb
    x=1-gamma
    u=[K(0),K(1)]; k=[K(1),K(2),K(-1)]
    c=[x,-gamma]
    d=[x-2*gamma,gamma] if rear else [x,-2*gamma]
    pc,pd,px=subst(L,c),subst(L,d),ev(L,x)
    if rear:
        F=sum_poly([mul([K(2),K(-1)],pc),sc(mul(u,pd),-1),
                    sc(mul(k,[K(-2),K(2)]),px)])
    else:
        H=[K(-2),K(1),K(4),K(-1)]; J=[K(2),K(3),K(-12),K(4)]
        F=sum_poly([sc(mul(J,pc),2),mul(H,pd),sc(mul(k,J),-px)])
    # Only structural gaps: a known nonzero diagonal, strict nonzero rear factor,
    # and actual pairwise distinct ordinary pegs. No Legendre value is divided.
    pegs=[[gamma*A],[gamma*B],[x],c,d]
    guards=[u,k]
    for i in range(len(pegs)):
        for j in range(i):
            r=add(pegs[i],sc(pegs[j],-1)); assert r
            guards.append(r)
    assert F
    gap=mon(guarded(F,guards))
    print('constant exact gap',front,M.degree(),rear,len(gap)-1,flush=True)
    return gap,(gamma,A,B,m,ha,hb,q,x)

def finite(front,M,rear,p,t):
    un,data=exact_gap(front,M,rear)
    if len(un)<=1:
        return 0
    fp=Bfield(nmod_poly([0,1],p),p,t)
    reduced=fp.cast(Epoly(M))
    assert reduced.degree()==M.degree() and reduced.leading_coefficient()==1
    count=0
    for m0,_ in reduced.factor()[1]:
        F=Bfield(m0,p,t); poly=list(map(F,un))
        assert len(poly)==len(un) and poly[-1]==F(1)
        K=Tower(poly); u=K.gen()
        g,A,B,m,ha,hb,q,x=map(K,data)
        c=x-g*u; d=x-g*(2-u if rear else 2*u)
        k=1+2*u-u*u
        g.inv(); k.inv(); q.inv()
        pegs=[g*A,g*B,x,c,d]
        for i,j in product(range(5),repeat=2):
            if i>j:
                (pegs[i]-pegs[j]).inv()
        L=mon(list(map(K,Lco))); lx,lc=ev(L,x),ev(L,c)
        # No division by L(x), L(c), or L(d); a Gauss peg is accounted for if present.
        R=[-c*k*lx+x*lc,k*lx-lc]
        W=[sum(L[j]/(j-i) for j in range(i+1,5)) for i in range(4)]
        V=sc(qr(mul(R,invpoly(K,W,L)),L)[1],-1)
        rows=[[ev(L,y)*y**j for j in range(4)]+[ev(V,y)] for y in pegs]
        rhs=[-ev(L,y)*y**4 for y in pegs]
        det0=det(rows)
        print('constant nodal pivot', front,rear,p,m0.degree(),len(un)-1,flush=True)
        dinv=det0.inv()
        u0,u1,u2,u3,lam=[v*dinv for v in cramer(rows,rhs)]
        D=add(mul(L,[u0,u1,u2,u3,K(1)]),sc(V,lam))
        W,rem=qr(D,nodal(pegs))
        assert not rem and len(W)==4 and W[-1]==K(1)
        assert all(ev(D,y)==0 for y in pegs)
        assert len(D)==9 and D[-1]==K(1)
        # Actual fifth differs from each ordinary peg, so belongs to the missing cubic.
        Y=[w*g**(i-3) for i,w in enumerate(W)]
        C=[K(v)*g**j/q for j,v in enumerate(Lco)]
        H4=[cv(K,w) for w in pol(h4(front),lambda x:x)]
        E=first5(K,A,B,m,ha,hb,C,H4)
        multicol(Y,E).inv()
        print('constant fifth unit',front,rear,p,m0.degree(),len(un)-1,flush=True)
        count+=1
    return count

if __name__=='__main__':
    pp,tt=1103,161
    assert isprime(pp) and (2*tt*tt-1)%pp==0
    counts=[]
    for f,r in product((True,False),repeat=2):
        factors=gamma_factors(f)
        assert [M.degree() for M in factors]==[4]
        n=sum(finite(f,M,r,pp,tt) for M in factors)
        counts.append(n)
        print('verified phase',f,r,n,flush=True)
    assert counts==[0,3,2,2]
    print('all four scoped constant-numerator phases excluded',flush=True)
