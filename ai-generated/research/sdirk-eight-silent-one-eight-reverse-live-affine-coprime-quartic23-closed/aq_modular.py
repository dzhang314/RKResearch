"""Complete monic reductions of the literal 2/3 affine quartic charts."""
from aq_gamma import projection, gpoly
from aq_rear import front_data,tail_data
from regular_star_projection import Co
from unequal_finite import Bfield,Tower,Lco,gcdp
from equal_undetected_front import Nested
from reverse_live_quartic import literal_fifth
from off8_fibers import add,sc,mul,nodal,qr,det,multicol,ev,trim,cramer
from extra_active import invpoly
from flint import nmod_poly

def lcmo(V,E):
    return trim([V(gpoly(q)) for q in E])
def mon(P):
    return sc(P,P[-1].inv())
def horner(q,x):
    s=0
    for a in q[::-1]:s=a+x*s
    return s
def sfifth(V,A,B,m,ha,hb,s,h,Q,L):
    H0=literal_fifth(V,A,B,m,ha,hb,s,h,[])
    H1=literal_fifth(V,A,B,m,ha,hb,s,h,[V(1)])
    Hs=add(H1,sc(H0,-1))
    R=add(mul(H0,Q),mul(Hs,L))
    W,err=qr(R,nodal([A,B,s]))
    assert not err and len(W)<=3
    return W

def fiber(front,rear,slot,p,t):
    F,G,J,gs=tail_data(front,rear,slot)
    M=projection(front,rear,slot)
    D=Bfield(nmod_poly([0,1],p),p,t).cast(M)
    assert D.degree()==M.degree() and D.leading_coefficient()==1
    A,B,m,ha,hb,H,H4,Q=front_data(front)[0]
    parts=D.factor()[1]
    check=nmod_poly([1],p)
    images=[]
    for MM,e in parts:
        check*=MM**e
    assert check==D
    for MM,e in parts:
        N=Bfield(MM,p,t); gamma=N(nmod_poly([0,1],p))
        Fn,Gn,Jn=[lcmo(N,Co(U,i)) for U,i in ((F,0),(G,0),(J,1))]
        assert len(Fn)==(3 if rear else 6) and len(Gn)==4 and len(Jn)==3
        Fn=mon(Fn);Jn=mon(Jn)
        End=gcdp(Fn,Gn)
        assert End and End[-1]==1
        images.append((MM.degree(),e,len(End)-1))
        if len(End)==1:continue
        U=Tower(End);u=U.gen()
        V=Nested(list(map(U,Jn)));s=V.gen()
        cv=lambda n:V(U(N(gpoly(n))))
        Gamma0,uu=V(U(gamma)),V(u)
        A0,B0,m0,Ha,Hb,Hd=map(cv,(A,B,m,ha,hb,H))
        Hs=horner(list(map(cv,H4)),s)
        x=1-Gamma0;c=x-Gamma0*uu;d=x-Gamma0*(2-uu if rear else 2*uu)
        pegs=[Gamma0*(B0 if slot==2 else A0),Gamma0*s,x,c,d]
        Q0=list(map(cv,Q));L0=list(map(V,Lco))
        WL=[sum(L0[j]/(j-i) for j in range(i+1,5)) for i in range(4)]
        X=invpoly(V,WL,mon(L0));Z=qr(mul(X,mul(Q0,Q0)),mon(L0))[1]
        rows=[];rhs=[]
        for a in pegs:
            L=ev(L0,a)
            rows.append([L,L*a,L*a*a,L*a**3,ev(Z,a)])
            rhs.append(-L*a**4)
        # Units, not merely nonzero elements, in the entire reduced fibre.
        pi=det(rows).inv()
        QY=[Q0[i]*Gamma0**i for i in range(2)]
        LY=[Gamma0*Hd*L0[i]*Gamma0**i for i in range(5)]
        J5=sfifth(V,A0,B0,m0,Ha,Hb,s,Hs,QY,LY)
        *Coef,lam=[v*pi for v in cramer(rows,rhs)]
        # The solved D8 has leading coefficient 70; normalize it to one.
        D8=add(mul(L0,Coef+[V(1)]),sc(Z,lam))
        D8=mon(D8)
        Miss,E=qr(D8,nodal(pegs));assert not E and len(Miss)==4
        Y0=[a*Gamma0**i/Gamma0**3 for i,a in enumerate(Miss)]
        multicol(Y0,J5).inv()
    assert sum(a*e for a,e,_ in images)==M.degree()
    print('complete affine modular',front,rear,slot,p,t,'diagonal degree',M.degree(),
          'all (diagonal degree,multiplicity,common gap degree)',images,flush=True)
    return (len(images),sum(a*e*u*2 for a,e,u in images))
