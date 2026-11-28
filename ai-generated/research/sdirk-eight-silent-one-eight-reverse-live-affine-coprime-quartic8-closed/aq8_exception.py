"""Retain the three actual fourth leading/contact strata separately."""
from aq8_projection import tail,fifth_project,exceptional_sources
from aq_rear import front_data
from aq_gamma import gpoly
from regular_star_projection import Co
from aq_modular import lcmo,mon,Bfield,nmod_poly,gcdp
from aq_modular import horner


def special(front,p,t):
    F,J,_,_,_=tail(front);RY=fifth_project(front)
    A0,B0=front_data(front)[0][:2]
    ans=[]
    for mode,H in enumerate(exceptional_sources(front)):
        M=gpoly(H).monic()
        V=Bfield(nmod_poly([0,1],p),p,t).cast(M)
        assert V.degree()==4 and V.leading_coefficient()==1
        parts=V.factor()[1]
        prod=nmod_poly([1],p)
        for K,e in parts:prod*=K**e
        assert prod==V
        n=0
        for K,e in parts:
            U=Bfield(K,p,t);g=U(nmod_poly([0,1],p))
            js=[U(gpoly(a)) for a in Co(J,1)]
            if mode==0:
                assert not js[2]
                s=-js[0]/js[1]
            else:
                a=U(gpoly(A0 if mode==1 else B0))
                assert horner(js,a)==0
                s=-js[1]/js[2]-a
            assert horner(js,s)==0
            fp=lcmo(U,Co(F))
            assert len(fp)==5
            # Polynomial in u at the actual, alternate fourth root.
            X=[horner([U(gpoly(c)) for c in Co(p,1)],s) for p in Co(RY)]
            E=gcdp(mon(fp),X)
            print('exceptional true fourth fiber',front,mode,K.degree(),e,'gap degree',len(E)-1,flush=True)
            assert len(E)==1
            n+=K.degree()*e
        assert n==4
        ans.append(n)
    return ans
