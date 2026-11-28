#!/usr/bin/env python3
"""Independent exact physical-coordinate vs homogeneous-row audit."""
import sympy as s
Y=s.Symbol('Y')
Q=s.Rational
def I(f):
    a=s.integrate(f,Y);return s.expand(a-a.subs(Y,0))
def at(f,y):return s.expand(f).subs(Y,y)
def use(f,i):return s.Poly(f,Y).nth(i)
def fit(f,m,r):return s.rem(s.expand(f*s.invert(m,r,Y)),r,Y)
j0=42*Y**4-84*Y**3+56*Y**2-14*Y+1
def rows(R,m,v,S):
    j=s.expand(S**4*j0.subs(Y,Y/S))
    P,P0=Y*m,Y*R
    L0,L1=I(P0)/Y,I(Y*P0)/Y
    ell,rho,w,u,f1=[fit(f,m,R) for f in (I(P)/Y,I(I(P))/Y,L0,j,L1)]
    c2,c0=use(R,2),use(R,0);r,sc=use(m,1),use(m,0)
    pp,qq=r*c0,3*sc*c2-4*r*sc-3*c0
    assert qq!=0
    z=pp/qq
    k=v*at(j,v)/at(u,v)
    d=(at(I(P0),v)-k*at(w,v))/at(P0,v)
    T=at(ell,v)*k-at(I(P),v)+d*(at(P,v)-k)
    pm1=(z-v)*T-at(I(I(P)),v)+at(rho,v)*k
    assert at(ell,z)==at(rho,z)==at(w,z)==0
    n=s.resultant(R,m,Y)
    M,W0,Q0,E,F=[s.expand(n*f) for f in (u,w,f1,ell,rho)]
    U=at(M,v); hv=v*at(j,v)
    d4=s.div(s.expand(L0*M-W0*j),R,Y)
    d5=s.div(s.expand(L1*M-Q0*j),R,Y)
    assert d4[1]==d5[1]==0
    cv=at(d4[0],v)
    assert cv==d*U
    pvin, ipv=at(P,v),at(I(P),v)
    np=(pp-v*qq)*((at(E,v)*hv-ipv*U)*U+cv*(pvin*U-n*hv))-qq*(at(I(I(P)),v)*U-at(F,v)*hv)*U
    assert np==qq*U**2*pm1
    K=(v-z)*(k-at(P,v))/at(P0,v)
    lam=s.expand((Y-z)*ell-rho+K*w)
    assert at(lam,z)==0 and use(lam,2)!=0
    x=-use(lam,1)/use(lam,2)-z
    cq=at(P0,v)*U
    kp=(qq*v-pp)*(n*hv-pvin*U)
    lamn=s.expand(cq*((qq*Y-pp)*E-qq*F)+kp*W0)
    assert lamn==s.expand(cq*qq*n*lam)
    xd,xp=qq*use(lamn,2),-qq*use(lamn,1)-pp*use(lamn,2)
    assert xd!=0 and xp==xd*x
    # Build the genuine primitive by old interpolation, its independent
    # V read and the first ghost zero, not the cross product.
    D=L1-v*L0
    mu=(at(D,v)*at(u,v)/at(j,v)-at(f1-v*w,v))/at(R,v)
    raw=f1-v*w+mu*R
    actual=s.expand(raw-at(raw,z)*u/at(u,z))
    assert at(actual,z)==0
    B=s.expand(at(j,v)*(Q0-v*W0)+(at(d5[0],v)-v*cv)*R)
    rb=s.expand(qq**3*(at(M,z)*B-at(B,z)*M))
    assert rb==s.expand(qq**3*at(M,z)*at(j,v)*n*actual)
    a1,a2,a3=(use(rb,i) for i in (1,2,3))
    qd=qq**2*a1+pp*qq*a2+pp**2*a3+(qq**2*a2+pp*qq*a3)*Y+qq**2*a3*Y**2
    assert s.expand((qq*Y-pp)*qd-qq**3*rb)==0
    pol,rem=s.div(actual,Y-z,Y); assert rem==0
    assert xd**2*at(qd,x)==qq**5*at(M,z)*at(j,v)*n*xd**2*at(pol,x)
    return pm1,x,z,actual
for r,sc,c2,v in [(2,1,4,Q(2,7)),(3,1,5,Q(4,7)),(4,3,7,Q(7,10)),(5,2,1,Q(2,5))]:
    r,sc,c2=map(Q,(r,sc,c2))
    c1=6*sc*(c2-r)/r
    c0=sc**2*(3*c2-4*r)/(r*r-3*sc)
    R=Y**3+c2*Y**2+c1*Y+c0;m=Y**2+r*Y+sc
    aa,xx,zz,qa=rows(R,m,v,1)
    S=Q(17,3)
    ab,xb,zb,qb=rows(s.expand(S**3*R.subs(Y,Y/S)),s.expand(S**2*m.subs(Y,Y/S)),S*v,S)
    assert (ab,xb,zb)==(S**5*aa,S*xx,S*zz)
    assert s.expand(qb-S**3*qa.subs(Y,Y/S))==0
print('Four exact independent old-profile checks; all horizontal scales and coefficient rows agree.')
