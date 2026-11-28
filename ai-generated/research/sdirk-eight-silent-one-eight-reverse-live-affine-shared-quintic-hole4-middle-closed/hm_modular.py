"""Full fibers retain actual b9=b10 as a fourth homogeneous coefficient row."""
from hm_projection import projection_data,diagonal,model
from aq_gamma import gpoly
from regular_star_projection import Co
from aq_modular import lcmo,mon,horner,Bfield,nmod_poly,gcdp
from aq_modular import ev as peval,nodal,det as smdet
from gauss_separate import span_unit
from arith_ordinary_reconstruction import extend,factor_deriv
from itertools import combinations

def evs0(B,P,s,I):
    return horner([I(B(gpoly(q))) for q in Co(P,1)],s)

def mode(front,rear,p,t):
    F,N,J,gs,pegs,cols=projection_data(front,rear)
    M,R0=diagonal(front,rear)
    H,den,Alp,Bet,_,vals=model(front)
    D=Bfield(nmod_poly([0,1],p),p,t).cast(M)
    assert D.degree()==M.degree() and D.leading_coefficient()==1
    parts=D.factor()[1]
    chk=nmod_poly([1],p)
    for U,e in parts:chk*=U**e
    assert chk==D
    ans=[]
    for MM,e in parts:
        N0=Bfield(MM,p,t)
        Sv,Rv=(lcmo(N0,Co(Q,1)) for Q in (J,R0))
        assert len(Sv)==4 and Sv[-1]==1
        S0=gcdp(Sv,Rv)
        assert len(S0)>1 and S0[-1]==1
        U,ss,inc0=extend(N0,S0)
        cv0=lambda v:evs0(N0,v,ss,inc0)
        F0,Nv=[[cv0(h) for h in Co(Q)] for Q in (F,N)]
        assert len(F0)==(3 if rear else 6)
        F0[-1].inv()
        Du=gcdp(F0,Nv)
        assert len(Du)>1 and Du[-1]==1
        V,u,inc1=extend(U,Du)
        cv=lambda f: horner([inc1(cv0(g0)) for g0 in Co(f)],u)
        a,b,x,c,d=map(cv,pegs)
        H0=list(map(cv,H))
        E=nodal([a,b,x,c,d]);ED=factor_deriv(E,V)
        A0=peval(H0,c)*peval(ED,c);B0=peval(H0,x)*peval(ED,x)
        row=[c**j*A0-x**j*B0 for j in range(3)]
        CC=[list(map(cv,v)) for v in cols]
        # Minimal signed RHS model: all 3x3 minors are necessary.
        rr=list(map(list,zip(*CC)))
        minors=[smdet([rr[a],rr[b],row]) for a,b in combinations(range(3),2)]
        span_unit(V,*minors)
        ans.append((MM.degree(),e,len(S0)-1,len(Du)-1))
    assert sum(d*e for d,e,_,_ in ans)==M.degree()
    print('corrected hole4 middle complete fibers',front,rear,p,t,ans,flush=True)
    return len(ans)
