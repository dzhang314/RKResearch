"""Full modular fibres and actual fifth at true ordinarily silent fourth."""
from aq4_projection import model, project
from aq_rear import front_data,Lco
from aq_gamma import gpoly
from regular_star_projection import Co
from aq_modular import lcmo,mon,horner,sfifth,Bfield,Tower,nmod_poly
from aq_modular import gcdp,qr,ev as peval,mul,sc,add,nodal,det,invpoly,multicol,cramer

def apply(B,f,u):
    return horner([u.A(B(gpoly(c))) for c in Co(f)],u)

def fiber(front,rear,p,t):
    F,G,J,n0,d0,_,data=model(front,rear)
    M=project(front,rear)
    D=Bfield(nmod_poly([0,1],p),p,t).cast(M)
    assert D.degree()==M.degree() and D.leading_coefficient()==1
    A,B,m,ha,hb,H,H4,Q=front_data(front)[0]
    parts=D.factor()[1]
    product_check=nmod_poly([1],p)
    for piece,e in parts:product_check*=piece**e
    assert D==product_check
    images=[]
    for MM,e in parts:
        N=Bfield(MM,p,t); gamma=N(nmod_poly([0,1],p))
        Fn,Gn=[lcmo(N,Co(P)) for P in (F,G)]
        assert len(Fn)==(3 if rear else 6)
        Fn=mon(Fn)
        E=gcdp(Fn,Gn)
        assert E and E[-1]==1
        images.append((MM.degree(),e,len(E)-1))
        if len(E)==1:continue
        U=Tower(E);u=U.gen()
        cv=lambda v:U(N(gpoly(v)))
        pn=lambda P:apply(N,P,u)
        den,num=pn(d0),pn(n0)
        gg=U(gamma);AA,BB,mm,HA,HB,HH=map(cv,(A,B,m,ha,hb,H))
        pegs=list(map(pn,data))
        Q0=list(map(cv,Q));L0=list(map(U,Lco))
        # Unit over the complete reduced F,G gap, not a nonzero scalar guess.
        s=num*den.inv()
        assert not horner(list(map(cv,Co(J,1))),s)
        W=[sum(L0[j]/(j-i) for j in range(i+1,5)) for i in range(4)]
        Z=qr(mul(invpoly(U,W,mon(L0)),mul(Q0,Q0)),mon(L0))[1]
        rows=[];rhs=[]
        for clock in pegs:
            L=peval(L0,clock)
            rows.append([L,L*clock,L*clock**2,L*clock**3,peval(Z,clock)])
            rhs.append(-L*clock**4)
        d0inv=det(rows).inv()
        *coef,lam=[n*d0inv for n in cramer(rows,rhs)]
        P=mon(add(mul(L0,coef+[U(1)]),sc(Z,lam)))
        Y,r0=qr(P,nodal(pegs));assert not r0 and len(Y)==4
        Yn=[z*gg**j/gg**3 for j,z in enumerate(Y)]
        QY=[Q0[j]*gg**j for j in range(2)];LY=[gg*HH*L0[j]*gg**j for j in range(5)]
        J5=sfifth(U,AA,BB,mm,HA,HB,s,horner(list(map(cv,H4)),s),QY,LY)
        multicol(Yn,J5).inv()
    assert sum(a*e for a,e,_ in images)==M.degree()
    print('complete affine coprime silent fourth',front,rear,p,t,'degree',M.degree(),
          'all (diagonal degree,multiplicity,common gap degree)',images,flush=True)
    return len(images),sum(a*e*u for a,e,u in images)
