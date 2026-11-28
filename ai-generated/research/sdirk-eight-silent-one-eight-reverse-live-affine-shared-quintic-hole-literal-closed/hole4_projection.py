"""Corrected quartic with actual ordinary hole at fourth, literal reverse-live silent 2/3."""
from functools import lru_cache
from aq_rear import C,u,s,g,red,ev,divide,front_data,Lco
from regular_star_projection import Co,con,remove
from aq5_projection import flip
from aq_gamma import gpoly
from small_crt import small_resultant, image, int_input
from hole_quintic_rank import Ls

def Kcoeff(r):
    return [red(sum((2*j+1)*p[i]*ev(p,r) for j,p in enumerate(Ls) if i<len(p))) for i in range(4)]

@lru_cache(None)
def model(front):
    (A,B,m,ha,hb,HD,H4,Q),_,_=front_data(front)
    a,b,r=red(g*A),red(g*B),g*s
    K=Kcoeff(r)
    La,Lb=ev(Lco,a),ev(Lco,b)
    Ka,Kb=ev(K,a),ev(K,b)
    den=red(La*Kb-Lb*Ka)
    Alp,Bet=red(ha*Kb-hb*Ka),red(La*hb-Lb*ha)
    H=[red(Alp*f+(Bet*K[j] if j<4 else 0)) for j,f in enumerate(Lco)]
    assert ev(H,a)==red(den*ha) and ev(H,b)==red(den*hb)
    G4=ev(H4,s)
    lc=H4[-1];lcN=red(lc*con(lc));assert lcN.is_constant()
    J=red(G4*con(lc)/lcN)
    assert Co(J,1)[-1]==1
    return H,den,Alp,Bet,J,(A,B,m,ha,hb,a,b,r)

@lru_cache(None)
def tail(front,rear,slot):
    H,den,Alp,Bet,J,dat=model(front)
    A,B,m,ha,hb,a,b,r=dat
    x=1-g;c=x-g*u;d=x-g*(2-u if rear else 2*u)
    k=1+2*u-u*u
    hp,hc,hd,hx=[ev(H,v) for v in (r,c,d,x)]
    G=divide(red((x-({2:a,3:b}[slot]))*hc-k*(c-({2:a,3:b}[slot]))*hx),u)
    if rear:
        raw=red((2-u)*hc-u*hd+(2*u-2)*k*hx)
        F=divide(raw,u*(u-1)*(u-2))
    else:
        Hr=-2+u+4*u*u-u**3
        Jr=2+3*u-12*u*u+4*u**3
        F=divide(red(Hr*hd+2*Jr*hc-k*Jr*hx),u*u)
    guards=(g,den,Alp,Bet,hp,hx,x-a,x-b)
    print('corrected hole4 tail shape',front,rear,slot,F.degrees(),G.degrees(),flush=True)
    return F,G,J,guards,(x,c,d,k)

def crt(A,B,j):
    D,E=A.degrees()[0],B.degrees()[0]
    cap=tuple(D*B.degrees()[k]+E*A.degrees()[k] for k in [2,1])
    q=image(int_input(A)[:2],int_input(B)[:2],1129,406,cap,(D,E))
    assert q and any(a for c in q for a in c), (j,cap)
    return small_resultant(A,B)

@lru_cache(None)
def diagonal(front,rear,slot):
    F,G,J,gs,_=tail(front,rear,slot)
    R=crt(F,G,'gap')
    R0,e=remove(R,(gs[0],gs[2]))
    assert e==[6 if rear else 7,1]
    assert R0.degrees()[:3]==(0,12 if rear else 21,40 if rear else 72)
    print('corrected hole4 gap exact',front,rear,slot,R.degrees(),R0.degrees(),e,flush=True)
    T=flip(crt(flip(J),flip(R0),'outer'))
    assert T.degrees()[:3]==(0,0,120 if rear else 216)
    print('corrected hole4 γ exact',front,rear,slot,T.degrees(),flush=True)
    return gpoly(T).monic(),R0
