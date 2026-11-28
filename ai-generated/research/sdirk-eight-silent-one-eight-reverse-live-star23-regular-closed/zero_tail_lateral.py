"""Rank-zero centered tail on literally silent physical two or three."""
from zero_tail_rank import ex_constants,model,ccols,QU,DU
from unequal_finite import Bfield,Tower
from equal_undetected_front import Nested
from off8_fibers import ev,mul,sc,nodal,det
from flint import nmod_poly
from math import comb

def test(slot,p,t):
    raw=nmod_poly([-5,18],p)*nmod_poly(list(DU),p)
    assert raw.degree()==5 and sorted((f.degree(),e) for f,e in raw.factor()[1])==[(1,1),(1,1),(3,1)]
    cs=0
    for M,e in raw.factor()[1]:
        K=Bfield(M,p,t);g=K(nmod_poly([0,1],p));g.inv()
        L,S,(A,B,ha,hb,H4)=model(K,g)
        U=Tower(sc(S,S[-1].inv()));s=U.gen();GL=list(map(U,L))
        gg=U(g);x=1-gg;m=1-2*gg;q=gg*s
        z=gg*U(A if slot==2 else B)
        hp=[sum(GL[i]*comb(i,j)*m**(i-j)*gg**j for i in range(j,6)) for j in range(6)]
        hx=ev(GL,x)
        assert not hp[4]+hp[5] and not hp[2]+hp[3]+hx
        P=[(x-z)*hp[0]-2*(m-z)*hx,(x-z)*hp[2]+(m-z)*hx,(x-z)*hp[4]]
        Z=Nested(sc(P,P[-1].inv()));w=Z.gen()
        W=Z(gg);X=Z(x);V=Z(m)
        other=W*Z(U(B if slot==2 else A))
        E=mul(nodal([other,Z(q),X]),[V*V-W*W*w,-2*V,Z(1)])
        H=list(map(Z,GL))
        N=det(ccols(E,H,Z))
        N.inv()
        print('lateral zero-tail exact unit',slot,p,t,M.degree(),flush=True)
        cs+=1
    return cs
