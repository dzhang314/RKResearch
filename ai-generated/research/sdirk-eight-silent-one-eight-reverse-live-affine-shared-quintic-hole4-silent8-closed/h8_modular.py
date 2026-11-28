"""Full signed hole4 silent8 fibers, retaining the actual zero h4."""
from h8_projection import diagonal,project,model
from aq_gamma import gpoly
from hole4_modular import W,evs0
from aq_modular import lcmo,mon,horner,Bfield,nmod_poly,gcdp
from aq_modular import ev as peval,qr,mul,sc,add,nodal,det as smdet,invpoly,cramer,multicol
from regular_star_projection import Co
from arith_ordinary_reconstruction import extend
from reverse_live_quartic import literal_fifth

def check(front,p,t):
    F,N,J,_,pegs=project(front)
    M,R0=diagonal(front)
    H,den,Alp,Bet,_,vals=model(front)
    A,B,m,ha,hb,a,b,r=vals
    D=Bfield(nmod_poly([0,1],p),p,t).cast(M)
    assert D.degree()==M.degree() and D.leading_coefficient()==1
    parts=D.factor()[1]
    chk=nmod_poly([1],p)
    for U,e in parts:chk*=U**e
    assert chk==D
    ans=[]
    for MM,e in parts:
        N0=Bfield(MM,p,t);gg=N0(nmod_poly([0,1],p))
        Sv,Rv=(lcmo(N0,Co(Q,1)) for Q in (J,R0))
        assert len(Sv)==4 and Sv[-1]==1
        S0=gcdp(Sv,Rv)
        assert len(S0)==2 and S0[-1]==1
        U,ss,inc0=extend(N0,S0)
        cv0=lambda v:evs0(N0,v,ss,inc0)
        F0,Nv=[[cv0(h) for h in Co(Q)] for Q in (F,N)]
        assert len(F0)==5
        F0[-1].inv()
        Du=gcdp(F0,Nv)
        assert len(Du)==2 and Du[-1]==1
        V,u,inc1=extend(U,Du)
        cv=lambda f: horner([inc1(cv0(g0)) for g0 in Co(f)],u)
        s=inc1(ss);g=inc1(inc0(gg))
        known=list(map(cv,pegs))
        pa,pb,x,c=known
        H0=list(map(cv,H));r0=g*s
        nu=cv(Bet)*peval(H0,r0).inv()
        Hm=mon(H0)
        WH=W(V,Hm,nu,r0)
        Inv=invpoly(V,WH,Hm)
        rows=[];rhs=[]
        for t0 in known:
            Lt=peval(Hm,t0)
            rows.append([Lt,Lt*t0,Lt*t0**2,peval(Inv,t0)])
            rhs.append(-Lt*t0**3)
        di=smdet(rows).inv()
        *pc,lam=[q*di for q in cramer(rows,rhs)]
        D7=add(mul(Hm,pc+[V(1)]),sc(Inv,lam))
        R7,rem=qr(D7,nodal(known));assert not rem and len(R7)==4
        Y=mon([v*g**i for i,v in enumerate(R7)])
        aa,bb,tr,ha0,hb0=map(cv,(A,B,m,ha,hb))
        HPoly=[p*g**i/cv(den) for i,p in enumerate(H0)]
        # True fourth is a hole: its literal amplitude is zero. Its continued
        # profile value is nonzero, so Y-s is not an allowed polynomial pad.
        F5=literal_fifth(V,aa,bb,tr,ha0,hb0,s,V(0),HPoly)
        J5,rem=qr(F5,nodal([aa,bb]))
        assert not rem and len(J5)<=4
        multicol(Y,J5).inv()
        ans.append((MM.degree(),e,len(S0)-1,len(Du)-1))
    assert sum(d*e for d,e,_,_ in ans)==M.degree()
    print('corrected ordinary hole4, full actual silent8 fibers',front,p,t,ans,flush=True)
    return len(ans)
