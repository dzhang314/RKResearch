"""Ordinary fifth with actual later silent row 6 or 7."""
from aq5_projection import six_peg,project_u,project_g
from aq_rear import front_data,Lco
from aq_gamma import gpoly
from regular_star_projection import Co
from aq_modular import (lcmo,mon,horner,sfifth,Bfield,Tower,nmod_poly,Nested,gcdp,
                        ev,qr,mul,sc,add,nodal,det,invpoly,multicol,cramer)
from aq4_modular import apply
from gauss_separate import span_unit

def unit(v):
    try:v.inv();return True
    except ArithmeticError:return False

def fibers(front,rear,p,t):
    F,J,P,_,_,_,pegs=six_peg(front,rear)
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
    tested=0
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
        gg=V(U(gamma));Pdet=pv(P)
        if unit(Pdet):continue
        aa,bb,mm,HA,HB,HH=map(cv,(A,B,m,ha,hb,H))
        known=list(map(pv,pegs))
        Q0=list(map(cv,Q));L0=list(map(V,Lco))
        WL=[sum(L0[j]/(j-i) for j in range(i+1,5)) for i in range(4)]
        Z=qr(mul(invpoly(V,WL,mon(L0)),mul(Q0,Q0)),mon(L0))[1]
        rows=[];rhs=[]
        for c in known:
            L=ev(L0,c)
            rows.append([L,L*c,L*c**2,L*c**3,ev(Z,c)])
            rhs.append(-L*c**4)
        # The fixed pivot uses only (a,b,q,x,c), not the third rear d.
        r,b=rows[:5],rhs[:5]
        delta_inv=det(r).inv()
        *coef,lam=[n*delta_inv for n in cramer(r,b)]
        D8=mon(add(mul(L0,coef+[V(1)]),sc(Z,lam)))
        Y,rem=qr(D8,nodal(known))
        assert len(Y)==3 and Y[-1]==1
        Y0=[c*gg**j/gg**2 for j,c in enumerate(Y)]
        QY=[cv(z)*gg**j for j,z in enumerate(Q)]
        LY=[gg*HH*V(Lco[j])*gg**j for j in range(5)]
        J5=sfifth(V,aa,bb,mm,HA,HB,s,horner(list(map(cv,H4)),s),QY,LY)
        assert len(J5)<=3
        a0,a1,a2=J5+[V(0)]*(3-len(J5))
        r0,r1=Y0[:2]
        aa0,aa1=a0-a2*r0,a1-a2*r1
        red_det=aa0**2-aa0*aa1*r1+aa1**2*r0
        assert red_det==multicol(Y0,J5)
        span_unit(V,Pdet,*rem,red_det)
        tested+=1
    assert sum(a*e for a,e,_ in images)==M.degree()
    print('affine coprime silent 6 or 7',front,rear,p,t,'diagonal degree',M.degree(),
          'all (diagonal degree,multiplicity,common gap degree)',images,
          'full missing quadratics tested',tested,flush=True)
    return (len(images),sum(a*e*u*2 for a,e,u in images),tested)
