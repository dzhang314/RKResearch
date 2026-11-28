"""Arithmetic ordinary hole8 with actual literal silent 2, 3 or 4."""
from aq_rear import C,u,s,g,red,ev,divide,front_data,Lco
from hole4_projection import Kcoeff,crt
from regular_star_projection import Co,remove
from aq_gamma import gpoly
from functools import lru_cache

@lru_cache(None)
def model(front):
    (A,B,m,ha,hb,HD,H4,Q),_,_=front_data(front)
    a,b=red(g*A),red(g*B)
    x=1-g;c=x-g*u;r=x-2*g*u
    K=Kcoeff(r)
    La,Lb=ev(Lco,a),ev(Lco,b)
    Ka,Kb=ev(K,a),ev(K,b)
    den=red(La*Kb-Lb*Ka)
    Alp,Bet=red(ha*Kb-hb*Ka),red(La*hb-Lb*ha)
    H=[red(Alp*f+(Bet*K[j] if j<4 else 0)) for j,f in enumerate(Lco)]
    assert ev(H,a)==red(den*ha) and ev(H,b)==red(den*hb)
    Phi=red(den*ev(H4,s)-ev(H,g*s))
    J=divide(Phi,red((s-A)*(s-B)))
    assert J.degrees()[1]==2
    return H,den,Alp,Bet,J,(A,B,m,ha,hb,H4,a,b,x,c,r)

def arithmetic_gap():
    return (2+3*u-12*u*u+4*u**3)/4

@lru_cache(None)
def proj(front,slot):
    H,den,Alp,Bet,J,dat=model(front)
    A,B,m,ha,hb,H4,a,b,x,c,r=dat
    F=arithmetic_gap()
    k=1+2*u-u*u
    Hx,Hc,Hr=map(lambda v:ev(H,v),(x,c,r))
    R=divide(red(Hc-k*Hx),u)
    n0,d0=red(x*R+g*k*Hx),red(g*R)
    if slot==4:
        # Actual silent fourth z=gamma*s; only the actual penultimate determines it.
        V=Co(J,1)
        P=red(sum(a*n0**j*d0**(2-j) for j,a in enumerate(V)))
    else:
        z={2:a,3:b}[slot]
        P=divide(red((x-z)*Hc-k*(c-z)*Hx),u)
    if slot==4:
        assert P.degrees()[:3]==(15,0,32)
        N,powers=remove(P,(g,))
        assert powers==[2] and N.degrees()[:3]==(15,0,30)
    else:
        N=P
        assert N.degrees()[:3]==(6,0,11)
    assert J.degrees()[:3]==(3,2,10)
    print('actual ordinary hole8 literal projection',front,slot,F.degrees(),J.degrees(),
          P.degrees(),N.degrees(),flush=True)
    return F,N,J,(n0,d0)

@lru_cache(None)
def diagonal(front,slot):
    F,N,_,_=proj(front,slot)
    P=crt(F,N,'literal ordinary hole8 diagonal')
    assert P.degrees()[:3]==(0,0,90 if slot==4 else 33)
    print('actual ordinary hole8 literal gamma',front,slot,P.degrees(),flush=True)
    return gpoly(P).monic()
