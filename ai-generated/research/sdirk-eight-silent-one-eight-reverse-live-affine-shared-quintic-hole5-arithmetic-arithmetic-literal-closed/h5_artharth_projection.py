"""Regular corrected hole5, arithmetic front with ordinary arithmetic rear."""
from functools import lru_cache
from h5_arthfront_projection import early
from h5_regular_projection import model,gpoly
from aq_rear import s as U,g,red,ev,divide
from regular_star_projection import Co,remove
from hole4_projection import crt
from aq5_projection import flip

@lru_cache(None)
def rear(slot):
    H,D,A,B,J,Z,gs,dat=model(False)
    a,b,r,x=dat[-4:]
    u=U;k=1+2*u-u*u;c=x-g*u;d=x-2*g*u
    z={2:a,3:b}[slot]
    hc,hd,hx=[ev(H,n) for n in (c,d,x)]
    G=divide(red((x-z)*hc-k*(c-z)*hx),u)
    Hr=-2+u+4*u*u-u**3;Jr=2+3*u-12*u*u+4*u**3
    F=divide(red(Hr*hd+2*Jr*hc-k*Jr*hx),u*u)
    return F,G,(c,d,k)

@lru_cache(None)
def diagonal(slot):
    H,D,A,B,J,Z,gs,dat=model(False)
    F,G,_=rear(slot)
    Q=flip(crt(flip(F),flip(G),'actual literal arithmetic rear fifth hole'))
    Q0,qe=remove(Q,gs)
    P=early()
    assert F.degrees()==(3,5,10,1) and G.degrees()==(3,3,11,1)
    assert Q.degrees()==(24,0,85,1) and Q0.degrees()==(21,0,72,1)
    assert qe==[7,0,1,0,0,0,0,0]
    print('arith/arith literal exact tail',slot,F.degrees(),G.degrees(),Q.degrees(),Q0.degrees(),qe,flush=True)
    R=crt(P,Q0,'real arithmetic-front literal ordinary arithmetic')
    R0,re=remove(R,tuple(g0 for g0 in gs if g0.degrees()[0]==0))
    M=gpoly(R0).monic()
    ns=lambda v:v.a*v.a-v.b*v.b/2
    norms=ns(gpoly(Co(P)[-1])).gcd(ns(gpoly(Co(Q0)[-1])))
    common=ns(M).gcd(norms)
    assert R.degrees()==(0,0,1539,1) and R0.degrees()==(0,0,1077,1)
    assert re==[210,63,0,0] and common.degree()==0
    print('arith/arith literal projected diagonal',slot,R.degrees(),R0.degrees(),re,'common Y-leading norm degree',common.degree(),flush=True)
    return M,P,Q0
