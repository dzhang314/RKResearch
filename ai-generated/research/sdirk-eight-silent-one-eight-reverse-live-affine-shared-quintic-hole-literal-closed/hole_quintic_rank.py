"""Four cheap exact early rank-loss models in the corrected shared quintic."""
from reverse_live_quartic import profile_gamma,L4
from aq_modular import Bfield,Tower,nmod_poly,mon,ev
Ls=((1,),(-1,2),(1,-6,6),(-1,12,-30,20))
def K3(x,r):return sum((2*j+1)*ev(P,x)*ev(P,r) for j,P in enumerate(Ls))
def rank_loss(front,p,t):
    D,data=profile_gamma(front,L4)
    F=Bfield(nmod_poly([0,1],p),p,t)
    M=nmod_poly([int(F(q).x[0]) for q in D],p)
    assert M.degree()==4 and M.leading_coefficient()==1
    G=nmod_poly([1],p);facts=M.factor()[1]
    for Q,j in facts:G*=Q**j
    assert G==M
    counts=[]
    for MM,e in facts:
        B=Bfield(MM,p,t);g=B(nmod_poly([0,1],p));x=1-g
        A,C,m,ha,hb,H4=data
        A,C,ha,hb=map(B,(A,C,ha,hb))
        qa,qb=g*A,g*C
        # Generic rank loss, before assuming any physical hole position.
        Rs=[sum((2*j+1)*B(P[i])*(ha*ev(P,qb)-hb*ev(P,qa))
                for j,P in enumerate(Ls) if i<len(P)) for i in range(4)]
        Rs[-1].inv()
        ar=Tower(mon(Rs));r=ar.gen()
        assert not (ar(ha)*K3(ar(qb),r)-ar(hb)*K3(ar(qa),r))
        for pos in (4,8):
            R=list(map(B,H4 if pos==4 else (2,3,-12,4)))
            assert len(R)==4
            U=Tower(mon(R));u=U.gen()
            z=U(g)*u if pos==4 else U(x)-2*U(g)*u
            residual=U(ha)*K3(U(qb),z)-U(hb)*K3(U(qa),z)
            residual.inv()
        counts.append((MM.degree(),e))
    print('corrected shared quintic early rank loss; finite general, impossible hole4/8',front,counts,flush=True)
    return counts
