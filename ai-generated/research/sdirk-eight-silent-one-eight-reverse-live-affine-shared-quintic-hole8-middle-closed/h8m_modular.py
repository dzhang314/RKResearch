"""Complete ordinary hole8 middle fibers tested by the paid equal-terminal row."""
from h8m_projection import projection_data,diagonal,model
from aq_gamma import gpoly
from aq_modular import lcmo,mon,horner,Bfield,nmod_poly,gcdp
from aq_modular import ev as peval,nodal,det as smdet
from regular_star_projection import Co
from gauss_separate import span_unit
from arith_ordinary_reconstruction import extend,factor_deriv
from itertools import combinations

def evu(B,F,u,I):
    return horner([I(B(gpoly(c))) for c in Co(F)],u)

def mode(front,p,t):
    F,N,J,gs,pegs,cols=projection_data(front)
    M,R=diagonal(front)
    H,den,Alp,Bet,_,vals=model(front)
    D=Bfield(nmod_poly([0,1],p),p,t).cast(M)
    assert D.degree()==M.degree() and D.leading_coefficient()==1
    parts=D.factor()[1]
    chk=nmod_poly([1],p)
    for B,e in parts:chk*=B**e
    assert chk==D
    ans=[]
    for MM,e in parts:
        B=Bfield(MM,p,t)
        Fn,Rn=[lcmo(B,Co(a)) for a in (F,R)]
        assert len(Fn)==4 and Fn[-1]==1
        E=gcdp(Fn,Rn)
        assert len(E)==2 and E[-1]==1
        U,u,i0=extend(B,E)
        cvu=lambda v:evu(B,v,u,i0)
        Jn=[cvu(a) for a in Co(J,1)]
        assert len(Jn)==3
        V,s,i1=extend(U,mon(Jn))
        cv=lambda a:horner([i1(cvu(v)) for v in Co(a,1)],s)
        pa,pb,q,x,c=map(cv,pegs)
        H0=list(map(cv,H))
        E5=nodal([pa,pb,q,x,c]);ED=factor_deriv(E5,V)
        Ac=peval(H0,c)*peval(ED,c);Ax=peval(H0,x)*peval(ED,x)
        Bk=[Ac*c**j-Ax*x**j for j in range(3)]
        signed=list(map(list,zip(*[list(map(cv,w)) for w in cols])))
        minors=[smdet([*signed])]+[smdet([signed[i],signed[j],Bk]) for i,j in combinations(range(3),2)]
        span_unit(V,*minors)
        ans.append((MM.degree(),e,len(E)-1,len(Jn)-1))
    assert sum(d*e for d,e,_,_ in ans)==M.degree()
    print('ordinary hole8 middle complete fibers',front,p,t,ans,flush=True)
    return len(ans)
