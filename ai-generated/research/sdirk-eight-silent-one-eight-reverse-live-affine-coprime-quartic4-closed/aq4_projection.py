"""Affine-coprime L4, actual silent fourth projected by the true penultimate read."""
from functools import lru_cache
from aq_rear import C,u,s,g,t,red,ev,divide,front_data,Lco
from regular_star_projection import Co,remove
from aq_gamma import gpoly
from small_crt import small_resultant

@lru_cache(None)
def model(front,rear):
    fd,J,gs=front_data(front)
    A,B,m,ha,hb,H,H4,Q=fd
    a,b=red(g*A),red(g*B)
    x=1-g;c=x-g*u;d=x-g*(2-u if rear else 2*u)
    k=1+2*u-u*u
    Px,Pc,Pd=[ev(Lco,y) for y in (x,c,d)]
    Qx,Qc,Qd=[ev(Q,y) for y in (x,c,d)]
    if rear:
        raw=red((2-u)*Pc*Qx*Qd-u*Pd*Qx*Qc+(2*u-2)*k*Px*Qc*Qd)
        F=divide(raw,u*(u-1)*(u-2))
    else:
        Hr=-2+u+4*u*u-u**3
        Jr=2+3*u-12*u*u+4*u**3
        raw=red(Hr*Pd*Qx*Qc+2*Jr*Pc*Qx*Qd-k*Jr*Px*Qc*Qd)
        F=divide(raw,u*u)
    R=divide(red(Pc*Qx-k*Px*Qc),u)
    n0,d0=red(x*R+g*k*Px*Qc),red(g*R)
    C0=Co(J,1)
    assert len(C0)==3 and d0
    N=red(sum(P*n0**j*d0**(2-j) for j,P in enumerate(C0)))
    L,st=remove(gs[4],gs[:4]);assert L.degrees()[2]==12 and st==[0,0,1,1]
    guards=gs+(Px,Qx,L,x-a,x-b)
    assert F.degrees()[:3]==(2 if rear else 5,0,14) and N.degrees()[:3]==(6,0,24)
    print('aq4 exact raw shapes',front,rear,F.degrees(),N.degrees(),
          flush=True)
    return F,N,J,n0,d0,guards,(a,b,x,c,d)

@lru_cache(None)
def project(front,rear):
    F,N,J,n0,d0,guards,_=model(front,rear)
    R=small_resultant(F,N)
    assert R and R.degrees()[:3]==(0,0,132 if rear else 204)
    M,e=remove(R,guards)
    assert e==[12 if rear else 14,0,2,2,0,0,4,2,0,0]
    M0=gpoly(M).monic()
    assert M0.degree()==(60 if rear else 130)
    print('aq4 exact gamma deg',front,rear,R.degrees()[2],M0.degree(),'guards',e,flush=True)
    return M0
