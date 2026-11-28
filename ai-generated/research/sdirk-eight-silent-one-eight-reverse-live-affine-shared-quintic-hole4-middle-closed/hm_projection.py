"""Signed five-nonhole-peg projections before actual silent 5, 6 or 7 release."""
from hole4_projection import model,tail,crt
from aq_rear import g,red,ev
from regular_star_projection import remove,nodal,det,cof,Z
from aq5_projection import flip
from aq_gamma import gpoly
from functools import lru_cache

def diff_read(P,hr,beta,r):
    return [red(sum(P[j]*(hr/(j-i)-beta*r**(j-i-1)) for j in range(i+1,len(P)))) for i in range(len(P)-1)]

def signed_columns(H,Bet,r,pegs,n):
    assert len(pegs)+n<=7
    E=nodal(list(pegs))
    H_r=ev(H,r)
    WH=diff_read(H,H_r,Bet,r)
    cols=[]
    for j in range(n+1):
        D=[Z]*j+E
        WD=diff_read(D,H_r,Bet,r)
        T=[red(cof(H,WD,i)-cof(D,WH,i)) for i in range(11)]
        assert all(not q for q in T[4:])
        cols.append(T[1:4])
    return tuple(cols)

@lru_cache(None)
def projection_data(front,rear):
    H,den,Alp,Bet,J,dat=model(front)
    A,B,m,ha,hb,a,b,r=dat
    # Reuse only the true ordinary-eighth shape F, never literal z=2 or 3.
    F,_,J,gs,(x,c,d,k)=tail(front,rear,2)
    pegs=(a,b,x,c,d)
    H_r=ev(H,r)
    cols=signed_columns(H,Bet,r,pegs,2)
    P=det(cols)
    H0,e=remove(H_r,(g,))
    assert e==[1] and H0.degrees()[:3]==(0,7,9)
    N,powers=remove(P,(g,Alp,H0))
    assert powers==[3,1,2] and N.degrees()[:3]==(6,13,36)
    assert P.degrees()[:3]==(6,30,63)
    print('corrected hole4 middle signed determinant',front,rear,P.degrees(),N.degrees(),powers,flush=True)
    return F,N,J,gs,pegs,tuple(cols)

@lru_cache(None)
def diagonal(front,rear):
    F,N,J,gs,pegs,cols=projection_data(front,rear)
    R=crt(F,N,'signed middle gap')
    R0,e=remove(R,(gs[0],gs[2]))
    assert e==[12,2]
    assert R.degrees()[:3]==(0,44 if rear else 83,132 if rear else 240)
    assert R0.degrees()[:3]==(0,38 if rear else 77,108 if rear else 216)
    print('corrected hole4 middle gap exact',front,rear,R.degrees(),R0.degrees(),e,flush=True)
    T=flip(crt(flip(J),flip(R0),'signed middle diagonal'))
    assert T.degrees()[:3]==(0,0,324 if rear else 648)
    print('corrected hole4 middle γ exact',front,rear,T.degrees(),flush=True)
    return gpoly(T).monic(),R0
