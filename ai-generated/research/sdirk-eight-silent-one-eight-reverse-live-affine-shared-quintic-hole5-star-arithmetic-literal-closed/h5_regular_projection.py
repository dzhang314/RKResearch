"""Regular corrected fifth hole with literal actual silent 2/3; exact nested projectors."""
from functools import lru_cache
from h5_zero import zero_fifth
from aq_rear import C,u as Y,s as S,g,red,ev,divide,Lco
from hole4_projection import Kcoeff,crt
from regular_star_projection import Co,remove
from aq5_projection import flip
from aq_gamma import gpoly

@lru_cache(None)
def model(front):
    Z,dat=zero_fifth(front)
    A,B,m,ha,hb,H4=dat
    a,b,r=red(g*A),red(g*B),g*Y
    K=Kcoeff(r)
    La,Lb=ev(Lco,a),ev(Lco,b)
    Ka,Kb=ev(K,a),ev(K,b)
    den=red(La*Kb-Lb*Ka)
    Alp,Bet=red(ha*Kb-hb*Ka),red(La*hb-Lb*ha)
    H=[red(Alp*f+(Bet*K[j] if j<4 else 0)) for j,f in enumerate(Lco)]
    assert ev(H,a)==red(den*ha) and ev(H,b)==red(den*hb)
    J=divide(red(den*ev(H4,S)-ev(H,g*S)),red((S-A)*(S-B)))
    x=1-g
    de,_=remove(den,(g,));hr,_=remove(ev(H,r),(g,))
    gs=(g,de,Alp,Bet,hr,ev(H,x),x-a,x-b)
    return H,den,Alp,Bet,J,Z,gs,(A,B,m,ha,hb,H4,a,b,r,x)

@lru_cache(None)
def front_cut(front):
    assert front
    H,den,Alp,Bet,J,Z,gs,dat=model(front)
    P=flip(crt(flip(J),flip(Z),'actual zero fifth and fourth'))
    P0,e=remove(P,(g,))
    assert e==[1] and P.degrees()[:3]==(11,0,10) and P0.degrees()[:3]==(11,0,9)
    print('corrected hole5 front exact',front,J.degrees(),Z.degrees(),P.degrees(),P0.degrees(),e,flush=True)
    return P0

@lru_cache(None)
def tail(front,rear,slot):
    assert front and not rear and slot in (2,3)
    H,den,Alp,Bet,J,Z,gs,dat=model(front)
    A,B,m,ha,hb,H4,a,b,r,x=dat
    u=S
    c=x-g*u;d=x-g*(2-u if rear else 2*u)
    k=1+2*u-u*u;z={2:a,3:b}[slot]
    hc,hd,hx=[ev(H,v) for v in (c,d,x)]
    G=divide(red((x-z)*hc-k*(c-z)*hx),u)
    Hr=-2+u+4*u*u-u**3;Jr=2+3*u-12*u*u+4*u**3
    F=divide(red(Hr*hd+2*Jr*hc-k*Jr*hx),u*u)
    assert F.degrees()[:3]==(3,5,10) and G.degrees()[:3]==(3,3,11)
    return F,G,(c,d,k)

@lru_cache(None)
def tail_cut(front,rear,slot):
    F,G,dat=tail(front,rear,slot)
    gs=model(front)[6]
    Q=flip(crt(flip(F),flip(G),'actual literal rear fifth hole'))
    Q0,e=remove(Q,(g,gs[2]))
    assert e==[7,1] and Q.degrees()[:3]==(24,0,85) and Q0.degrees()[:3]==(21,0,72)
    print('corrected hole5 rear exact',front,rear,slot,F.degrees(),G.degrees(),Q.degrees(),Q0.degrees(),e,flush=True)
    return Q0

@lru_cache(None)
def diagonal(front,rear,slot):
    P=front_cut(front);Q=tail_cut(front,rear,slot)
    M=crt(P,Q,'actual hole5 literal diagonal')
    gs=model(front)[6]
    M0,e=remove(M,(g,gs[3]))
    assert e==[84,21] and M.degrees()[:3]==(0,0,897) and M0.degrees()[:3]==(0,0,729)
    print('corrected hole5 diagonal exact',front,rear,slot,M.degrees(),M0.degrees(),e,flush=True)
    return gpoly(M0).monic()
