"""Regular corrected fifth-hole literal cases; all projected root fibers."""
from h5_regular_projection import (front_cut,tail_cut,model,diagonal,tail,g)
from aq_gamma import gpoly
from regular_star_projection import Co
from h5_rank_check import signed_rows
from aq_modular import lcmo,mon,horner,Bfield,nmod_poly,gcdp
from aq_modular import ev as peval,det
from arith_ordinary_reconstruction import extend
from gauss_separate import span_unit
from itertools import combinations

def unit(x):
    try:x.inv();return True
    except ArithmeticError:return False

def rrpow(B,P,y,I):
    return horner([I(B(gpoly(v))) for v in Co(P,0)],y)

def fiber(front,rear,slot,p,t):
    P=front_cut(front);Q=tail_cut(front,rear,slot)
    F,G,data=tail(front,rear,slot)
    H,den,Alp,Bet,J,Z,gs,lit=model(front)
    A,B0,m,ha,hb,H4,a,b,r,x=lit
    M=diagonal(front,rear,slot)
    D=Bfield(nmod_poly([0,1],p),p,t).cast(M)
    assert D.degree()==M.degree() and D.leading_coefficient()==1
    parts=D.factor()[1]
    chk=nmod_poly([1],p)
    for U,e in parts:chk*=U**e
    assert chk==D
    done=[]
    for MM,e in parts:
        B=Bfield(MM,p,t)
        P0,Q0=[lcmo(B,Co(T)) for T in (P,Q)]
        assert len(P0)==P.degrees()[0]+1 or len(Q0)==Q.degrees()[0]+1
        E=gcdp(P0,Q0)
        assert len(E)>1 and E[-1]==1
        U,y,I=extend(B,E)
        cvy=lambda T:rrpow(B,T,y,I)
        js,zs=[[cvy(v) for v in Co(T,1)] for T in (J,Z)]
        assert unit(js[-1]) or unit(zs[-1])
        Ss=gcdp(js,zs)
        assert len(Ss)>1 and Ss[-1]==1
        V,s,I0=extend(U,Ss)
        fu,gu=[list(map(I0,[cvy(v) for v in Co(T,1)])) for T in (F,G)]
        assert unit(fu[-1]) or unit(gu[-1])
        Rr=gcdp(fu,gu)
        assert len(Rr)>1 and Rr[-1]==1
        W,u,I1=extend(V,Rr)
        cv=lambda T:I1(I0(cvy(T)))
        cvu=lambda T:horner([cv(v) for v in Co(T,1)],u)
        a0,b0,x0,r0,g0,be=map(cv,(a,b,x,r,g,Bet))
        c0,d0,k=map(cvu,data)
        pegs=[a0,b0,g0*I1(s),x0,c0,d0];pegs.pop(slot-2)
        H0=list(map(cv,H))
        rows,Ec=signed_rows(W,H0,be,r0,pegs)
        Ac=peval(H0,c0)*peval(Ec,c0);Ax=peval(H0,x0)*peval(Ec,x0)
        rows.append([Ac*c0**j-Ax*x0**j for j in range(3)])
        span_unit(W,*[det(list(A)) for A in combinations(rows,3)])
        done.append((MM.degree(),e,len(E)-1,len(Ss)-1,len(Rr)-1))
    assert sum(a*e for a,e,*_ in done)==M.degree()
    print('regular fifth hole literal full star-arithmetic',slot,p,t,done,flush=True)
    return len(done)
