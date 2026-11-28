"""Actual affine-coprime/quartic early and tail projection, literal silent 2/3."""
from functools import lru_cache
from regular_star_projection import C,v as u,s,g,t,red,cast,ev,con
from unequal_finite import Lco
from seven_k0_anchors import cv,F2,ends,h4,pol

def divide(P,D):
    if D.degrees()[3]:
        D0=con(D)
        P,D=red(P*D0),red(D*D0)
    A,R=divmod(P,red(D))
    assert not R,(P.degrees(),D.degrees())
    return A

@lru_cache(None)
def front_data(front):
    A,B,m=map(lambda w:cast(cv(F2,w)),ends(front,1))
    ha,hb=red((A-1)/2),red((B-1-m)/2)
    H=red((B-A)*ha*hb)
    a,b=red(g*A),red(g*B)
    La,Lb=ev(Lco,a),ev(Lco,b)
    q0,q1=red(B*hb*La-A*ha*Lb),red(ha*Lb-hb*La)
    Q=[red(g*q0),q1]
    H4=[cast(cv(F2,w)) for w in pol(h4(front),lambda x:x)]
    M=red(ev(H4,s)*ev([q0,q1],s)-H*ev(Lco,g*s))
    M=divide(M,red((s-A)*(s-B)))
    gauss=red(sum(Lco[j]*(-Q[0])**j*Q[1]**(4-j) for j in range(5)))
    assert La and Lb and q1 and gauss and H
    return (A,B,m,ha,hb,H,H4,Q),M,(g,q1,La,Lb,gauss)

@lru_cache(None)
def tail_data(front,rear,slot):
    assert slot in (2,3)
    (A,B,m,ha,hb,H,H4,Q),M,gs=front_data(front)
    a,b=red(g*A),red(g*B)
    x=1-g
    c=x-g*u
    d=x-g*(2-u if rear else 2*u)
    z={2:a,3:b}[slot]
    k=1+2*u-u*u
    Px,Pc,Pd=[ev(Lco,y) for y in (x,c,d)]
    Qx,Qc,Qd=[ev(Q,y) for y in (x,c,d)]
    # Literal A or B is the actual ordinarily silent clock, still reverse-live.
    G=divide(red((x-z)*Pc*Qx-k*(c-z)*Px*Qc),u)
    if rear:
        R=red((2-u)*Pc*Qx*Qd-u*Pd*Qx*Qc+(2*u-2)*k*Px*Qc*Qd)
        F=divide(R,u*(u-1)*(u-2))
    else:
        Hr=-2+u+4*u*u-u**3
        Jr=2+3*u-12*u*u+4*u**3
        R=red(Hr*Pd*Qx*Qc+2*Jr*Pc*Qx*Qd-k*Jr*Px*Qc*Qd)
        F=divide(R,u*u)
    # Only actual parameter guards. In particular no degree assumption on F,G,M.
    gs=gs+(x-z,Px,Qx,x-a,x-b)
    print('tail exact shape',front,rear,slot,F.degrees(),G.degrees(),M.degrees(),flush=True)
    return F,G,M,gs
