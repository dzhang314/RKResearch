"""Actual silent stage five in the full six-ordinary-peg projection."""
from aq5_projection import six_peg,project_u,project_g
from aq_rear import front_data,Lco
from aq_gamma import gpoly
from regular_star_projection import Co
from aq_modular import lcmo,mon,horner,sfifth,Bfield,Tower,nmod_poly,Nested,gcdp,ev as peval
from aq4_modular import apply
from gauss_separate import span_unit

def unit(v):
    try:v.inv();return True
    except ArithmeticError:return False

def fibers(front,rear,p,t):
    F,J,P,n0,d0,_,_=six_peg(front,rear)
    N=project_u(front,rear)
    M=project_g(front,rear)
    D=Bfield(nmod_poly([0,1],p),p,t).cast(M)
    assert D.degree()==M.degree() and D.leading_coefficient()==1
    A,B,m,ha,hb,H,H4,Q=front_data(front)[0]
    parts=D.factor()[1]
    product_check=nmod_poly([1],p)
    for piece,e in parts:product_check*=piece**e
    assert D==product_check
    images=[]
    determinant_only=literal=0
    for MM,e in parts:
        N0=Bfield(MM,p,t); gamma=N0(nmod_poly([0,1],p))
        Fn,Nn,Jn=[lcmo(N0,Co(T,j)) for T,j in ((F,0),(N,0),(J,1))]
        assert len(Fn)==(3 if rear else 6) and len(Jn)==3
        Fn,Jn=mon(Fn),mon(Jn)
        E=gcdp(Fn,Nn)
        assert E and E[-1]==1
        images.append((MM.degree(),e,len(E)-1))
        if len(E)==1:continue
        U=Tower(E);u=U.gen()
        V=Nested(list(map(U,Jn)));s=V.gen()
        cv=lambda n:V(U(N0(gpoly(n))))
        pv=lambda f:horner([V(apply(N0,h,u)) for h in Co(f,1)],s)
        gg=V(U(gamma));den,num=pv(d0),pv(n0)
        aa,bb,mm,HA,HB,HH=map(cv,(A,B,m,ha,hb,H))
        pd=pv(P)
        if unit(pd):
            determinant_only+=1
            continue
        # This is the actual silent fifth, not an ordinary root.
        y=num*den.inv()
        QY=[cv(z)*gg**j for j,z in enumerate(Q)];LY=[gg*HH*V(Lco[j])*gg**j for j in range(5)]
        J5=sfifth(V,aa,bb,mm,HA,HB,s,horner(list(map(cv,H4)),s),QY,LY)
        span_unit(V,pd,peval(J5,y))
        literal+=1
    assert sum(a*e for a,e,_ in images)==M.degree()
    print('affine coprime silent fifth',front,rear,p,t,'degree',M.degree(),
          'all (diagonal degree,multiplicity,common gap degree)',images,
          'determinant-only and joint cuts',determinant_only,literal,flush=True)
    return (len(images),sum(a*e*u*2 for a,e,u in images),determinant_only,literal)
