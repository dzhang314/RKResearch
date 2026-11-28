"""Corrected ordinary fourth hole and actual silent eighth: signed terminal determinant."""
from functools import lru_cache
from aq_rear import g,u,red,ev,divide
from hole4_projection import model,crt
from hm_projection import signed_columns
from regular_star_projection import remove,det
from aq5_projection import flip
from aq_gamma import gpoly

@lru_cache(None)
def project(front):
    H,den,Alp,Bet,J,dat=model(front)
    A,B,m,ha,hb,a,b,r=dat
    x=1-g;c=x-g*u;k=1+2*u-u*u
    B=2*u+k*(u-2)
    Hx,Hc,Hr=[ev(H,v) for v in (x,c,r)]
    F=divide(red((u-2)*Hc-B*Hx),u)
    pegs=(a,b,x,c)
    Cs=signed_columns(H,Bet,r,pegs,3)
    # After the actual paid b9=b10 row combine the actual silent8 affine gap.
    Z=[red(B*(c-a)*(c-b)*c**j+(u-2)*(x-a)*(x-b)*x**j) for j in range(4)]
    P=det([w+[v] for w,v in zip(Cs,Z)])
    Hr0,e=remove(Hr,(g,))
    assert e==[1]
    guards=(g,Alp,Hr0,Hx)
    Delta0,e0=remove(den,(g,))
    assert e0==[1] and Delta0.degrees()[:3]==(0,3,9)
    N,ex=remove(P,(g,Alp,Hr0,Delta0))
    assert ex==[3,1,2,1] and F.degrees()[:3]==(4,3,10)
    assert P.degrees()[:3]==(11,30,65) and N.degrees()[:3]==(11,10,29)
    print('corrected hole4 silent8 determinant',front,F.degrees(),P.degrees(),N.degrees(),ex,flush=True)
    return F,N,J,guards,pegs

@lru_cache(None)
def diagonal(front):
    F,N,J,gs,pegs=project(front)
    R=crt(F,N,'corrected hole4 actual silent8 gap')
    R0,e=remove(R,(gs[0],gs[1],gs[3]))
    assert e==[16,2,3] and R.degrees()[:3]==(0,73,226) and R0.degrees()[:3]==(0,58,168)
    print('corrected hole4 silent8 gap',front,R.degrees(),R0.degrees(),e,flush=True)
    T=flip(crt(flip(J),flip(R0),'corrected hole4 actual silent8 γ'))
    assert T.degrees()[:3]==(0,0,504)
    print('corrected hole4 silent8 diagonal',front,T.degrees(),flush=True)
    return gpoly(T).monic(),R0
