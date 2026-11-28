#!/usr/bin/env python3
"""A genuinely paid split-free grade-seven crossing at the zero-diagonal E row."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'dirk12-fifteen-rank3-invisible-split-free-grid'))
from grid import (F, aggregate_weights, card_taps, derivative_hull, diff_lag,
                  forward_pair, lagrange, leg_deriv, reverse_seed, third_and_next_ratios)

def crossing(a,x,y,t_f,f_f,d,v,chart,leg_root=False):
    r=v/d
    t,g,h10,L,k,hv,h9=reverse_seed(r)
    u=d*t;w=1-a*f_f;e=1-a*t_f
    ordinary=[1-a*z for z in (1,x,y,t_f,f_f)]
    assert 0 not in ordinary
    sites=[F(0),F(1)]+ordinary+[d,v,u]
    assert len(set(sites))==10
    D=sites if chart==10 else sites[1:]
    B=aggregate_weights(sites)
    der=lambda s:derivative_hull(D,s)
    rho=B[d]*d**3*der(d)/6 if chart==10 else B[v]*d**4*hv*der(v)
    Hv=lambda s:rho/der(s)
    h=lambda s:Hv(s)/(B[s]*d**(3 if chart==10 else 4))
    hW,hE=h(w),h(e)
    w0,e0=w/d,e/d
    sig=F(1,6);one=F(1)
    CN,loE,loZ,_=third_and_next_ratios(chart,r,w0,hW)
    def sr(X,A,m):
        return sum(t**m*j for t,j in zip(X,A))
    j=2 if chart==10 else 1
    if chart==10:
        p1=r*r*(r+1)/(3*(2*r-1))
        pr=r*(4*r-5)/(6*(2*r-1))
        phi=lambda z:r+1+(F(1,2)-r)*z
        chi=lambda z:lagrange([0,one,r],[r*r+r+1,F(9,5),(p1+r**4*pr-r**5/5)/g],z)
        X=[one,r,t,w0]
        A=card_taps([one,r,t],t,h10,[phi(t)*h10])
        U=card_taps(X,w0,hW,[phi(w0)*hW,chi(w0)*hW])
        V=card_taps(X,e0,hE,[phi(e0)*hE,chi(e0)*hE])
        ee=[F(15,7),(p1+r**6*pr-r**7/7)/g,(r**5-1)/(r-1),
            (sr([one,r,t],A,6)-t**7/7)/h10,
            (sr(X,U,6)-w0**7/7)/hW,(sr(X,V,6)-e0**7/7)/hE]
        hiZ=[F(1,2),(sig*p1+r**3*g*pr)/g,(r**2*g-sig)/(r-1)]
        a0=[sig,g,h10,hW]
        for ht,coeff in zip([h10,hW,hE],[A,U,V]):
            hiZ.append(sum(z**3*m*v for z,m,v in zip(X,a0,coeff))/ht)
        loZe=sum(z**2*m*v for z,m,v in zip(X,a0,V))/hE
    else:
        assert chart==9
        p1=r**3/(6*(r-1));pr=r/2-p1/r
        a2=F(1,2)+1/(6*(r-1))+k
        phi=lambda z:lagrange([one,r],[(r*r+r-F(4,5))/k,(p1+r**4*pr-r**5/5)/hv],z)
        psi1=a2+hv/(r*(r-1)*k)
        X=[one,r,t,w0]
        A=card_taps([one,r,t],t,0,[L*h9])
        U=card_taps(X,w0,0,[L*hW,phi(w0)*hW])
        V=card_taps(X,e0,0,[L*hE,phi(e0)*hE])
        ee=[((r**5-1)/(r-1)-F(15,7))/k,
            (p1+r**6*pr-r**7/7)/hv,(sr(X,A,6)-t**7/7)/h9,
            (sr(X,U,6)-w0**7/7)/hW,(sr(X,V,6)-e0**7/7)/hE]
        hiZ=[psi1+(r+1)*hv/(r*k),r**2*pr]
        a0=[hv,h9,hW]
        for ht,coeff in zip([h9,hW,hE],[A,U,V]):
            hiZ.append((k*(ht-sig*coeff[0])+sum(z*z*m*v for z,m,v in zip(X[1:],a0,coeff[1:])))/ht)
        loZe=(k*(hE-sig*V[0])+sum(z*m*v for z,m,v in zip(X[1:],a0,V[1:])))/hE
    nodes=CN+[e0]; zz=loZ+[loZe]
    P=lambda n,s:(1-s)*leg_deriv(n,1-s)
    moment=lambda n:sum(B[s]*s**6*P(n,s) for s in sites)
    bary=lambda n,i:sum(Hv(s)*s**i*P(n,s) for s in D)
    # Test paid barycentric constants even over exact finite residue algebras.
    assert bary(6,j+1)==5544*rho and bary(7,j)==-24024*rho
    assert not bary(5,j+1) and not bary(6,j)
    assert rho
    q6=moment(6)/(5544*rho)
    alpha,gamma=forward_pair(a,x,y,leg_root)
    assert gamma
    beta=((alpha/gamma)*moment(5)+moment(7)-q6*bary(7,j+1))/(-24024*rho)
    v=[p-q6*z1-(beta/d)*z0 for p,z1,z0 in zip(ee,hiZ,zz)]
    return diff_lag(nodes,v)

if __name__=="__main__":
    for chart in (9,10):
        result=crossing(F(1,3),F(4,5),F(9,7),F(7,5),F(3,2),F(1,20),F(3,20),chart)
        assert result
    print("rho pivot, exact alpha/gamma path, and grade-seven crossing in both rational negative controls")
