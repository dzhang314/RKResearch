"""Full rank-two actual ordinary fourth hole, reverse-live literal silence 2 or 3."""
from hole4_projection import model,tail,diagonal
from aq_gamma import gpoly
from regular_star_projection import Co
from aq_modular import lcmo,mon,horner,Bfield,nmod_poly,gcdp
from aq_modular import ev as peval,qr,mul,sc,add,nodal,det,invpoly,cramer
from arith_ordinary_reconstruction import extend,factor_deriv

def W(V,P,nu,r):
    return [sum(P[j]*(V(1)/(j-i)-nu*r**(j-i-1)) for j in range(i+1,len(P))) for i in range(len(P)-1)]

def fibers(front,rear,slot,p,t):
    HS,den,Alp,Bet,J,vals=model(front)
    A,B,m,ha,hb,a,b,r=vals
    F,G,_,gs,back=tail(front,rear,slot)
    M,R0=diagonal(front,rear,slot)
    D=Bfield(nmod_poly([0,1],p),p,t).cast(M)
    assert D.degree()==M.degree() and D.leading_coefficient()==1
    parts=D.factor()[1]
    chk=nmod_poly([1],p)
    for U,e in parts:chk*=U**e
    assert chk==D
    ans=[]
    for MM,e in parts:
        N0=Bfield(MM,p,t);gg=N0(nmod_poly([0,1],p))
        Sv,Rv=(lcmo(N0,Co(Z,1)) for Z in (J,R0))
        assert len(Sv)==4 and Sv[-1]==1
        S0=gcdp(Sv,Rv)
        assert len(S0)>1 and S0[-1]==1
        U,ss,inc0=extend(N0,S0)
        cv0=lambda v:evs0(N0,v,ss,inc0)
        G0,F0=[[cv0(h) for h in Co(Q)] for Q in (G,F)]
        assert len(G0)==4 and len(F0)==(3 if rear else 6)
        G0[-1].inv();F0[-1].inv()
        Du=gcdp(G0,F0)
        assert len(Du)>1 and Du[-1]==1
        V,u,inc1=extend(U,Du)
        cv=lambda f: horner([inc1(cv0(z)) for z in Co(f)],u)
        g=inc1(inc0(gg));s=inc1(ss)
        x,c,d,k=map(cv,back);R,pa,pb=map(cv,(r,a,b))
        H=list(map(cv,HS));H0=peval(H,R)
        nu=cv(Bet)*H0.inv()
        Hm=mon(H)
        WH=W(V,Hm,nu,R)
        Inv=invpoly(V,WH,Hm)
        pegs=[pb if slot==2 else pa,x,c,d]
        rows=[];rhs=[]
        for t0 in pegs:
            Lt=peval(Hm,t0)
            rows.append([Lt,Lt*t0,Lt*t0**2,peval(Inv,t0)])
            rhs.append(-Lt*t0**3)
        di=det(rows).inv()
        *pc,lam=[q*di for q in cramer(rows,rhs)]
        D7=add(mul(Hm,pc+[V(1)]),sc(Inv,lam))
        R7,rem=qr(D7,nodal(pegs));assert not rem and len(R7)==4
        WV=W(V,D7,nu,R);DD=factor_deriv(D7,V)
        Bt=peval(WV,c)*peval(DD,x)-peval(WV,x)*peval(DD,c)
        Bt.inv()
        ans.append((MM.degree(),e,len(S0)-1,len(Du)-1))
    assert sum(d*e for d,e,_,_ in ans)==M.degree()
    print('ordinary hole4 plus actual silent 2/3',front,rear,slot,p,t,ans,flush=True)
    return len(ans)

def evs0(B,P,s,I):
    return horner([I(B(gpoly(q))) for q in Co(P,1)],s)
