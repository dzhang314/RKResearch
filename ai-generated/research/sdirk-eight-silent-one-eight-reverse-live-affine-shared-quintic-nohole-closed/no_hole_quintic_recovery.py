"""Six true ordinary pegs give both affine RHS coefficients."""
from no_hole_quintic_model import model,fifth,L4
from aq_modular import ev,qr,mul,sc,add,nodal,mon,invpoly
from equal_undetected_front import Nested

def factor_deriv(P,V):return [V(j)*a for j,a in enumerate(P[1:],1)]

def W(P):return [sum(P[j]/(j-i) for j in range(i+1,len(P))) for i in range(len(P)-1)]

def recovery(V,pegs):
    assert len(pegs)==6
    L=mon(list(map(V,L4)));J=invpoly(V,W(L),L)
    J1=qr([V(0)]+J,L)[1]
    E=nodal(pegs)
    Dr=factor_deriv(E,V)
    C0=[];C1=[]
    for a in pegs:
        Y,rem=qr(E,[-a,V(1)]);assert not rem
        T=sc(Y,(ev(Dr,a)*ev(L,a)).inv())
        C0=add(C0,sc(T,ev(J,a)))
        C1=add(C1,sc(T,ev(J1,a)))
    C0+=[V(0)]*(6-len(C0));C1+=[V(0)]*(6-len(C1))
    E0,F0=C0[5],C1[5];E1,F1=C0[4],C1[4]
    inv=(E0*F1-F0*E1).inv()
    la,mu=F0*inv,-E0*inv
    coeff=add(sc(C0,-la),sc(C1,-mu))
    assert len(coeff)==5 and coeff[-1]==1
    D=add(mul(L,coeff),add(sc(J,la),sc(J1,mu)))
    R,rr=qr(D,nodal(pegs));assert not rr and len(R)==3 and R[-1]==1
    return D

def first_back_gate(V,D,c,x):
    Dr=factor_deriv(D,V);WD=W(D)
    return ev(WD,c)*ev(Dr,x)-ev(WD,x)*ev(Dr,c)

def middle(front,rear,p,t):
    # Ordinary rows are 2,3,4,8,9,10 together with fifth and exactly one of 6,7.
    factors=[]
    for V,dat,_,_,dims in model(front,rear,p,t):
        g,x,c,d,u,k,a,b,q=dat
        D=recovery(V,[a,b,q,x,c,d])
        first_back_gate(V,D,c,x).inv()
        factors.append(dims)
    print('shared quintic no-hole: silent six or seven',front,rear,factors,flush=True)
    return len(factors)

def eighth(front,p,t):
    factors=[]
    for V,dat,LP,fr,dims in model(front,None,p,t):
        g,x,c,z,u,k,a,b,q=dat
        F=fifth(V,LP,fr)
        assert len(F)==3
        # Whole actual ordinary fifth quadratic; no root selected or lost.
        Y=Nested(mon(F));y=Y.gen()
        g,x,c,a,b,q=map(Y,(g,x,c,a,b,q))
        D=recovery(Y,[a,b,q,x,c,g*y])
        first_back_gate(Y,D,c,x).inv()
        factors.append(dims)
    print('shared quintic no-hole: actual silent eighth',front,factors,flush=True)
    return len(factors)
