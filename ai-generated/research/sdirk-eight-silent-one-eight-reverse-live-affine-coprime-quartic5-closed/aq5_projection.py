"""Exact six ordinary pegs projection for affine-coprime reverse-live quartic."""
from functools import lru_cache
from aq_rear import C,s,g,red,front_data,Lco
from aq4_projection import model as tail
from regular_star_projection import remove,nodal,det,mul,W,cof,Z
from aq_gamma import gpoly
from small_crt import small_resultant, int_input, image

def flip(F):
    return C.from_dict({(j,i,v,t):q for (i,j,v,t),q in F.to_dict().items()})

@lru_cache(None)
def six_peg(front,rear):
    F,_,J,n0,d0,gs,(a,b,x,c,d)=tail(front,rear)
    A,B,m,ha,hb,H,H4,Q=front_data(front)[0]
    q=g*s
    E=nodal([a,b,q,x,c,d])
    L=list(map(C.constant,Lco))
    WL=W(L);V=[]
    for j in range(3):
        D=[Z]*j+E;WD=W(D)
        Bz=[red(cof(L,WD,i)-cof(D,WL,i)) for i in range(4)]
        assert all(not red(cof(L,WD,i)-cof(D,WL,i)) for i in range(4,12))
        V.append(Bz)
    V.append(mul(Q,Q)+[Z])
    assert all(len(v)==4 for v in V)
    P=det(V)
    # Divide only the two true nonzero early quartic values.
    Lad,Lbd=gs[2:4]
    P0,powers=remove(P,(Lad,Lbd))
    assert powers==[1,1] and P.degrees()[:3]==(6,3,28) and P0.degrees()[:3]==(6,3,20)
    print('six peg determinant',front,rear,P.degrees(),P0.degrees(),powers,flush=True)
    return F,J,P0,n0,d0,gs,(a,b,q,x,c,d)

@lru_cache(None)
def project_u(front,rear):
    F,J,P,n0,d0,gs,pegs=six_peg(front,rear)
    N=flip(small_resultant(flip(J),flip(P)))
    R,H=remove(N,(gs[7],))
    assert N.degrees()[:3]==(12,0,52) and R.degrees()[:3]==(12,0,40) and H==[1]
    print('six peg exact gap projection',front,rear,N.degrees(),R.degrees(),H,flush=True)
    return R

@lru_cache(None)
def project_g(front,rear):
    F,J,P,n0,d0,gs,*_=six_peg(front,rear)
    N=project_u(front,rear)
    f0,n0=F.degrees()[0],N.degrees()[0]
    Cap=(f0*N.degrees()[2]+n0*F.degrees()[2],0)
    probe=image(int_input(F)[:2],int_input(N)[:2],1129,406,Cap,(f0,n0))
    assert probe and any(a for z in probe for a in z)
    R=small_resultant(F,N)
    assert R and R.degrees()[:3]==(0,0,248 if rear else 368)
    M,H=remove(R,(gs[0],gs[2],gs[3],gs[7]))
    assert H==[24,4,4,4] and M.degrees()[:3]==(0,0,144 if rear else 264)
    print('six peg exact γ projection',front,rear,R.degrees(),M.degrees(),H,flush=True)
    return gpoly(M).monic()
