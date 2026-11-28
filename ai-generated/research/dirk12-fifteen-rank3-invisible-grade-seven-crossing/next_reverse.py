#!/usr/bin/env python3
"""Actual next reverse singleton at E=1-e, with its forced zero diagonal."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'dirk12-fifteen-rank3-invisible-split-free-grid'))
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'dirk12-fifteen-rank3-invisible-fourth-supported-mask'))
from grid import (F, aggregate_weights, card_taps, derivative_hull, diff_lag,
                  hull, integ, lagrange, reverse_seed, third_and_next_ratios)
from tail import ordinary_read

def next_gates(a,x,y,t_f,f_f,d,v,chart,leg_root=False):
    r=v/d
    t,g,h10,L,k,hv,h9=reverse_seed(r)
    u=d*t;w=1-a*f_f;e=1-a*t_f
    assert w and e and e!=w
    ordinary=[1-a*z for z in (1,x,y,t_f,f_f)]
    assert 0 not in ordinary
    sites=[F(0),F(1)]+ordinary+[d,v,u]
    assert len(set(sites))==10
    D=sites if chart==10 else sites[1:]
    B=aggregate_weights(sites)
    der=lambda s:derivative_hull(D,s)
    rho=B[d]*d**3*der(d)/6 if chart==10 else B[v]*d**4*hv*der(v)
    assert rho
    h=lambda s:rho/(B[s]*der(s)*d**(3 if chart==10 else 4))
    hW,hE=h(w),h(e)
    w0,e0=w/d,e/d
    X=[F(1),r,t,w0]
    sig=F(1,6);one=F(1)
    if chart==10:
        p1=r*r*(r+1)/(3*(2*r-1))
        pr=r*(4*r-5)/(6*(2*r-1))
        phi=r+1+(F(1,2)-r)*e0
        chi=lagrange([0,one,r],[r*r+r+1,F(9,5),(p1+r**4*pr-r**5/5)/g],e0)
        psi=lagrange([0,one,r],[(g-sig)/(r-1),F(1,2),(sig*p1+r*g*pr)/g],e0)
        A=card_taps(X,e0,hE,[phi*hE,chi*hE])
        Z=sum(j*j*v*c for j,v,c in zip(X,[sig,g,h10,hW],A))
        lift=sum(j*v*c for j,v,c in zip(X,[sig,g,h10,hW],A))-psi*hE
    else:
        assert chart==9
        p1=r**3/(6*(r-1));pr=r/2-p1/r
        a2=F(1,2)+1/(6*(r-1))+k
        phi=lagrange([one,r],[(r*r+r-F(4,5))/k,(p1+r**4*pr-r**5/5)/hv],e0)
        psi=lagrange([one,r],[a2+hv/(r*(r-1)*k),pr],e0)
        A=card_taps(X,e0,0,[L*hE,phi*hE])
        dh=k*(hE-sig*A[0])
        Z=dh+r*hv*A[1]+t*h9*A[2]+w0*hW*A[3]
        lift=dh+hv*A[1]+h9*A[2]+hW*A[3]-psi*hE
    E=sum(j**5*c for j,c in zip(X,A))-e0**6/6
    nodes,RR,ZZ,_=third_and_next_ratios(chart,r,w0,hW)
    CE,CZ=diff_lag(nodes,RR),diff_lag(nodes,ZZ)
    interp=lagrange(nodes[:-1],
        [CZ*i-CE*j for i,j in zip(RR[:-1],ZZ[:-1])],e0)
    cross=CZ*E-CE*Z-interp*hE
    P=hull([0,1,x,y]);K=hull([0,1,x,y,t_f]);ev=lambda pol,T:sum(c*T**i for i,c in enumerate(pol))
    Kf=ev(K,f_f)
    forward=B[w]*a*(ordinary_read(a,x,y,P,f_f,leg_root)*Kf
                            -ordinary_read(a,x,y,K,f_f,leg_root)*ev(P,f_f))
    reverse=d*B[e]*A[3]*ev(P,t_f)*Kf
    return dict(lift=lift,cross=cross,fifth_from_fourth=forward-reverse)

def third_forward_gates(a,x,y,t_f,f_f,d,v,chart,leg_root=False):
    r=v/d
    t,g,h10,L,k,hv,h9=reverse_seed(r)
    u=d*t;w=1-a*f_f;e=1-a*t_f;c=1-a*y
    assert c and e and w
    ordinary=[1-a*z for z in (1,x,y,t_f,f_f)]
    assert 0 not in ordinary
    sites=[F(0),F(1)]+ordinary+[d,v,u]
    assert len(set(sites))==10
    D0=sites if chart==10 else sites[1:]
    B=aggregate_weights(sites);der=lambda s:derivative_hull(D0,s)
    rho=B[d]*d**3*der(d)/6 if chart==10 else B[v]*d**4*hv*der(v)
    assert rho
    hh=lambda s:rho/(B[s]*der(s)*d**(3 if chart==10 else 4))
    hW,hE,hC=hh(w),hh(e),hh(c)
    z,t0,w0,e0,c0=0,t,w/d,e/d,c/d
    X=[F(1),r,t0,w0]
    D=2*x*y-x-3*y*y+2*y
    omega=y*(x-y)*(y-1)/(2*D)
    own=a*omega/d
    P=hull([0,1,x,y]);K=hull([0,1,x,y,t_f])
    Q=hull([0,1,x]);norm=y*(y-1)*(y-x);Q=[v/norm for v in Q]
    def current(V,clock):return ordinary_read(a,x,y,V,clock,leg_root)
    ac_to_e=a*current(Q,t_f)
    tapE=ac_to_e*B[e]/(d*B[c])
    X0=X+[e0,c0];T0=[tapE,own]
    sig=F(1,6);one=F(1)
    if chart==10:
        p1=r*r*(r+1)/(3*(2*r-1))
        pr=r*(4*r-5)/(6*(2*r-1))
        phi=r+1+(F(1,2)-r)*c0
        chi=lagrange([0,one,r],[r*r+r+1,F(9,5),(p1+r**4*pr-r**5/5)/g],c0)
        psi=lagrange([0,one,r],[(g-sig)/(r-1),F(1,2),(sig*p1+r*g*pr)/g],c0)
        defects=[hC,phi*hC,chi*hC]
    else:
        assert chart==9
        p1=r**3/(6*(r-1));pr=r/2-p1/r
        a2=F(1,2)+1/(6*(r-1))+k
        phi=lagrange([one,r],[(r*r+r-F(4,5))/k,(p1+r**4*pr-r**5/5)/hv],c0)
        psi=lagrange([one,r],[a2+hv/(r*(r-1)*k),pr],c0)
        defects=[0,L*hC,phi*hC]
    A=[]
    for q in X:
        S=hull([0]+[p for p in X if p!=q])
        ev0=lambda pol,v:sum(t*v**j for j,t in enumerate(pol))
        Aj=integ(S,c0)+sum(S[j+2]*r0 for j,r0 in enumerate(defects))
        Aj-=tapE*ev0(S,e0)+own*ev0(S,c0)
        A.append(Aj/ev0(S,q))
    U=A+T0
    if chart==10:
        Z=sum(j*j*v*r0 for j,v,r0 in zip(X0,[sig,g,h10,hW,hE,hC],U))
        lift=sum(j*v*r0 for j,v,r0 in zip(X0,[sig,g,h10,hW,hE,hC],U))-psi*hC
    else:
        dh=k*(hC-sig*A[0])
        hv0=[hv,h9,hW,hE,hC]
        Z=dh+sum(j*v*r0 for j,v,r0 in zip(X0[1:],hv0,U[1:]))
        lift=dh+sum(v*r0 for v,r0 in zip(hv0,U[1:]))-psi*hC
    E=sum(j**5*v for j,v in zip(X0,U))-c0**6/6
    nodes,RR,ZZ,_=third_and_next_ratios(chart,r,w0,hW)
    CE,CZ=diff_lag(nodes,RR),diff_lag(nodes,ZZ)
    interp=lagrange(nodes[:-1],[CZ*i-CE*j for i,j in zip(RR[:-1],ZZ[:-1])],c0)
    def ev(pol,T):return sum(c*T**i for i,c in enumerate(pol))
    diag=a*current(K,f_f)/ev(K,f_f)
    tapFE=(a*current(P,f_f)-diag*ev(P,f_f))/ev(P,t_f)
    tapFC=a*current(Q,f_f)-tapFE*ev(Q,t_f)-diag*ev(Q,f_f)
    return dict(lift=lift,cross=CZ*E-CE*Z-interp*hC,
                direct=B[w]*tapFC-d*B[c]*A[3])

if __name__=="__main__":
    for chart in (9,10):
        args=(F(1,3),F(4,5),F(9,7),F(7,5),F(3,2),F(1,20),F(3,20),chart)
        assert all(next_gates(*args).values())
        assert all(third_forward_gates(*args).values())
    print("literal E/C forward/reverse and paid low/mixed arithmetic in both rational negative controls")
