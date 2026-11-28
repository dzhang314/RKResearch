"""Full early Rank-loss fifth hole algebra before any late assumptions."""
from h5_zero import zero_fifth
from reverse_live_quartic import profile_gamma,L4
from hole_quintic_rank import K3,Ls
from aq_modular import lcmo,Bfield,nmod_poly,mon,horner,ev,sc,add
from aq_gamma import gpoly
from regular_star_projection import Co
from arith_ordinary_reconstruction import extend

def rank_models(front,p,t):
    DG,data=profile_gamma(front,L4)
    F=Bfield(nmod_poly([0,1],p),p,t)
    M=nmod_poly([int(F(q).x[0]) for q in DG],p)
    assert M.degree()==4 and M.leading_coefficient()==1
    parts=M.factor()[1];prd=nmod_poly([1],p)
    for Q,e in parts:prd*=Q**e
    assert prd==M
    Z,_=zero_fifth(front)
    for F0,e in parts:
        B=Bfield(F0,p,t);g=B(nmod_poly([0,1],p))
        A,C,m,ha,hb,H4=data
        A,C,m,ha,hb=map(B,(A,C,m,ha,hb));H4=list(map(B,H4))
        a,b=g*A,g*C
        P=[sum((2*j+1)*B(L[i])*(ha*ev(L,b)-hb*ev(L,a))
               for j,L in enumerate(Ls) if i<len(L)) for i in range(4)]
        assert len(P)==4
        U,r,I=extend(B,mon(P));Y=r/I(g)
        # Substitute actual Y=r/gamma in the independent exact zero-fifth determinant.
        L=[horner(list(map(I,lcmo(B,Co(v)))),Y) for v in Co(Z,1)]
        assert len(L)==(2 if front else 4)
        V,s,J=extend(U,mon(L))
        i0=lambda z:J(I(z))
        a,b,g,ha,hb,A,C,m=map(i0,(a,b,g,ha,hb,A,C,m))
        r=J(r);Y=J(Y);q=g*s
        hq=ev(list(map(i0,H4)),s)
        L4v=list(map(V,L4))
        La,Lq=ev(L4v,a),ev(L4v,q)
        Ka,Kq=K3(a,r),K3(q,r)
        den=La*Kq-Lq*Ka
        alp=ha*Kq-hq*Ka;bet=La*hq-Lq*ha
        Hr=[V(0)]*4
        for j,L0 in enumerate(Ls):
            for i,c in enumerate(L0):Hr[i]+=(2*j+1)*c*ev(L0,r)
        H=add(sc(L4v,alp),sc(Hr,bet))
        for z in (den,alp,bet,ev(H,r),ev(H,1-g)):z.inv()
        print('ordinary fifth rank loss, full gamma/r/s degrees',front,F0.degree(),3,len(L)-1,flush=True)
        yield V,(g,a,b,q,r,A,C,s,m,ha,hb,hq,den,alp,bet),H,(F0.degree(),e)
