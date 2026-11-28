"""Signed four-known-peg checks for actual literal normally silent 2/3/4."""
from h8l_projection import model,proj,diagonal
from aq_gamma import gpoly
from regular_star_projection import Co
from hole4_modular import W
from aq_modular import lcmo,mon,horner,Bfield,nmod_poly,gcdp
from aq_modular import ev as peval,qr,mul,sc,add,nodal,det,invpoly,cramer
from arith_ordinary_reconstruction import extend,factor_deriv

def check(front,slot,p,t):
    F,N,J,nd=proj(front,slot)
    M=diagonal(front,slot)
    H,den,Alp,Bet,_,dat=model(front)
    A,B,m,ha,hb,H4,a,b,x,c,r=dat
    D=Bfield(nmod_poly([0,1],p),p,t).cast(M)
    assert D.degree()==M.degree() and D.leading_coefficient()==1
    parts=D.factor()[1]
    chk=nmod_poly([1],p)
    for U,e in parts:chk*=U**e
    assert chk==D
    ans=[]
    for MM,e in parts:
        N0=Bfield(MM,p,t);gg=N0(nmod_poly([0,1],p))
        S,Nv=(lcmo(N0,Co(Q,0)) for Q in (F,N))
        assert len(S)==4 and S[-1]==1
        D0=gcdp(S,Nv)
        assert len(D0)==2 and D0[-1]==1
        U,uu,inc0=extend(N0,D0)
        cv0=lambda P:horner([inc0(N0(gpoly(q))) for q in Co(P)],uu)
        JU=[cv0(P) for P in Co(J,1)]
        if slot==4:
            ss=cv0(nd[0])*cv0(nd[1]).inv()
            assert not horner(JU,ss)
            V,inc1,sd=U,U,1
        else:
            assert len(JU)==3
            V,ss,inc1=extend(U,mon(JU))
            sd=2
        cv=lambda f:inc1(cv0(f))
        g=inc1(inc0(gg));u=inc1(uu)
        pa,pb,X,C,R=map(cv,(a,b,x,c,r))
        q=g*ss
        H0=list(map(cv,H))
        nu=cv(Bet)*peval(H0,R).inv()
        Hm=mon(H0)
        WH=W(V,Hm,nu,R)
        Inv=invpoly(V,WH,Hm)
        pegs=[pa,pb,q,X,C];pegs.pop(slot-2)
        rows=[];rhs=[]
        for t0 in pegs:
            Lt=peval(Hm,t0)
            rows.append([Lt,Lt*t0,Lt*t0**2,peval(Inv,t0)])
            rhs.append(-Lt*t0**3)
        di=det(rows).inv()
        *pc,lam=[q*di for q in cramer(rows,rhs)]
        D7=add(mul(Hm,pc+[V(1)]),sc(Inv,lam))
        R7,rem=qr(D7,nodal(pegs));assert not rem and len(R7)==4
        WD=W(V,D7,nu,R);DD=factor_deriv(D7,V)
        Bt=peval(WD,C)*peval(DD,X)-peval(WD,X)*peval(DD,C)
        Bt.inv()
        ans.append((MM.degree(),e,len(D0)-1,sd))
    assert sum(d*e for d,e,_,_ in ans)==M.degree()
    print('ordinary hole8, full literal fibers',front,slot,p,t,ans,flush=True)
    return len(ans)
