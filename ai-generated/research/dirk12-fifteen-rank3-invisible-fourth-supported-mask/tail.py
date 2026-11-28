#!/usr/bin/env python3
"""Extra split-free literal gates at fifth/sixth ordinary live rows.

The protected optional w=0 branch of nine sites is excluded by the
separate exact first-root/nonroot packs, never evaluated here by division.
"""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/
                    "dirk12-fifteen-rank3-invisible-split-free-grid"))
from grid import (F, aggregate_weights, card_taps, derivative_hull,
                  exact_rref, hull, integ, lagrange, leg_deriv, reverse_seed)


def ordinary_read(a,x,y,P,s,leg_root):
    """Actual centered input degree <=5; normalized ordinary matrix."""
    assert len(P)<=6 and P[0]==0 and (leg_deriv(6,a)==0)==leg_root
    D=2*x*y-x-3*y*y+2*y
    I=integ(P);I1=integ([0]+P)
    if not leg_root:
        assert sum(P)==0
        R=lambda t:t*leg_deriv(6,a*t)/leg_deriv(6,a)
        G=lambda i,t:t*leg_deriv(i,a*t)-R(t)*leg_deriv(i,a)
        theta=-y**3*(y-1)**3*(3*x*x-2*x*y-2*x+y)/(x**3*(x-1)**3*D)
        A,C=exact_rref([[G(j,t) for j in [5,7]] for t in [x,y]],[1,theta])
        V=A*G(5,s)+C*G(7,s)
        return integ(P,s)-R(s)*I-V*(integ(P,x)-R(x)*I)
    DB=5*x*x-5*x+1
    ep=-(7*x*x-7*x+2)/1260
    rb=x**3*(15*x**3-49*x*x+55*x-20)/DB
    kb=-30*x**3*(x-1)**3/DB
    P0=hull([0,1,x,y]);f0=integ(P0);f1=integ([0]+P0)
    hi=integ([0,0]+P0)-ep
    ry,_=exact_rref([[f0,f1],[f1,hi]],[integ(P0,y),integ([0]+P0,y)])
    coeff=exact_rref([[t*leg_deriv(j,a*t) for j in [5,6,7]] for t in [1,x,y]],
                    [1,rb,ry])
    rs=s*sum(v*leg_deriv(j,a*s) for v,j in zip(coeff,[5,6,7]))
    ks=kb*s*leg_deriv(6,a*s)/(x*leg_deriv(6,a*x))
    return integ(P,s)-rs*I-ks*(I1-ep*(P[5] if len(P)==6 else 0))


def actual_w_row(chart,r,w,hw):
    """Four nonzero-source taps and the genuine grade-five lift residual."""
    t,g,h10,L,k,hv,h9=reverse_seed(r)
    sig=F(1,6);one=F(1);X=[one,r,t,w]
    assert w and hw
    if chart==10:
        p1=r*r*(r+1)/(3*(2*r-1))
        pr=r*(4*r-5)/(6*(2*r-1))
        phi=lambda z:r+1+(F(1,2)-r)*z
        chi=lambda z:lagrange([0,one,r],
            [r*r+r+1,F(9,5),(p1+r**4*pr-r**5/5)/g],z)
        psi=lagrange([0,one,r],[(g-sig)/(r-1),F(1,2),(sig*p1+r*g*pr)/g],w)
        A=card_taps(X,w,hw,[phi(w)*hw,chi(w)*hw])
        return A,sum(z*h*co for z,h,co in zip(X,[sig,g,h10,hw],A))-psi*hw
    assert chart==9
    p1=r**3/(6*(r-1))
    pr=r/2-p1/r
    a2=F(1,2)+1/(6*(r-1))+k
    phi=lagrange([one,r],[(r*r+r-F(4,5))/k,(p1+r**4*pr-r**5/5)/hv],w)
    psi=lagrange([one,r],[a2+hv/(r*(r-1)*k),pr],w)
    A=card_taps(X,w,0,[L*hw,phi*hw])
    return A,k*(hw-sig*A[0])+hv*A[1]+h9*A[2]+hw*A[3]-psi*hw


def tail_gates(a,x,y,t_f,f_f,d,v,chart,leg_root=False):
    r=v/d
    t,g,h10,L,k,hv,h9=reverse_seed(r)
    u=d*t;w=1-a*f_f
    assert w, "w=0 requires its separate nine-site exclusion"
    early=[1-a*z for z in [1,x,y,t_f,f_f]]
    labels=list(dict.fromkeys([F(0),F(1)]+early+[d,v,u]))
    dup=chart==10 or 0 in early
    D=labels if dup else [z for z in labels if z!=0]
    assert len(D)==chart and all(1-a*z!=1 for z in (1,x,y,t_f,f_f))
    B=aggregate_weights(labels)
    der=lambda s:derivative_hull(D,s)
    rho=B[d]*d**3*der(d)/6 if chart==10 else B[v]*d**4*hv*der(v)
    hw=rho/(B[w]*der(w)*d**(3 if chart==10 else 4))
    A,lift=actual_w_row(chart,r,w/d,hw)
    P=hull([0,1,x,y,t_f]);Pf=sum(c*f_f**j for j,c in enumerate(P))
    Qf=ordinary_read(a,x,y,P,f_f,leg_root)
    Qg=ordinary_read(a,x,y,P,(1-u)/a,leg_root)
    assert Pf!=0 and B[u]!=0
    return dict(lift=lift,fifth_diagonal=a*Qf-d*A[-1]*Pf,
                sixth_from_fifth=a*B[u]*Qg-d*B[w]*A[-2]*Pf,
                fifth_diag_forward=a*Qf/Pf,fifth_diag_reverse=d*A[-1])


if __name__=="__main__":
    for m in (9,10):
        v=tail_gates(F(1,3),F(4,5),F(9,7),F(7,5),F(3,2),F(1,20),F(3,20),m)
        assert all(v[k]!=0 for k in ["lift","fifth_diagonal","sixth_from_fifth"])
    print("both nonzero-w literal tap paths (rational negative controls)")
