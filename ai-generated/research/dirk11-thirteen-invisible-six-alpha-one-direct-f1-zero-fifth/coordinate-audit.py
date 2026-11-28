"""Independent exact rational coordinate audit of the direct F1 gates."""
from fractions import Fraction
import sympy as S
Y=S.symbols('Y')
rat=S.Rational
I=lambda f:S.Poly(S.integrate(f,Y),Y).as_expr()
ev=lambda f,v:S.expand(f).subs(Y,v)
fcoef=lambda f,j:S.Poly(f,Y).nth(j)
def audit(r,s,z,V,B,C,kap,t,q):
    z=r*s/(r*r-6*s)
    c0=-4*z*s/5; c1=6*s/5-4*z*r/5; c2=16*r/15-4*z/5
    R=Y**3+c2*Y**2+c1*Y+c0; m=kap*(Y**2+r*Y+s)
    P=Y*m; P0=Y*R
    J4=C**4-14*C**3*Y+56*C*C*Y*Y-84*C*Y**3+42*Y**4
    n=S.resultant(m,R,Y)
    mi=S.invert(m,R,Y)
    fit=lambda f:S.rem(mi*f,R,Y)
    L0=S.cancel(I(P0)/Y); L1=S.cancel(I(Y*P0)/Y)
    M,W,Q=map(fit,(J4,L0,L1))
    e,rho=map(fit,(S.cancel(I(P)/Y),S.cancel(I(I(P))/Y)))
    assert S.expand(e-(z-Y))==0 and ev(W,z)==ev(rho,z)==0
    assert 96*s**3-80*c1*s*s+75*c0*c2*s-75*c0*c0==0
    assert 16*r*s==15*(c2*s-c0)
    j=ev(J4,V);h=V*j;u0=n*M+t*R;u=ev(u0,V)
    p=q*z
    cv=ev(S.cancel((L0*n*M-n*W*J4)/R),V)+t*ev(L0,V)
    pv=ev(P0,V);pp=ev(P,V); iz=ev(u0,z); k=n*h/u;d=cv/u
    K=(V-z)*(k-pp)/pv
    l=(Y-z)*e-rho+K*W
    lnum=pv*u*((q*Y-p)*n*e-q*n*rho)+(q*V-p)*(n*h-pp*u)*n*W
    assert S.expand(lnum-q*n*pv*u*l)==0
    xd=q*fcoef(lnum,2);xn=-(q*fcoef(lnum,1)+p*fcoef(lnum,2));x=xn/xd
    assert x!=z and ev(l,x)==0
    T=ev(e,V)*k-ev(I(P),V)+d*(pp-k)
    Adj=(p-V*q)*((n*ev(e,V)*h-ev(I(P),V)*u)*u+cv*(pp*u-n*h))-q*(ev(I(I(P)),V)*u-n*ev(rho,V)*h)*u
    assert Adj==q*u*u*((z-V)*T-(ev(I(I(P)),V)-ev(rho,V)*k))
    D=L1-V*L0
    D5=S.cancel((L1*n*M-n*Q*J4)/R)
    B5=j*n*(Q-V*W)+(ev(D5,V)+t*ev(L1,V)-V*cv)*R
    Buf=n*(Q-V*W)+(ev(D,V)*u/j-n*ev(Q-V*W,V))/ev(R,V)*R
    assert S.expand(B5-j*Buf)==0
    Qeff=(Buf-ev(Buf,z)*u0/iz)/n
    Qnum=q**3*(iz*B5-ev(B5,z)*u0)
    Qpin=xd**2*q**2*ev(Qnum,x)/(x-z)
    assert Qpin==xd**2*q**5*iz*j*n*ev(Qeff,x)/(x-z)
    Cq=-d*d*u/(n*j)*(R-ev(R,z)*u0/iz)
    M0=j*q**3*iz*ev(q*n*S.cancel(W/(Y-z)),x)*q*((x-V)*u-cv)-cv*cv*q**5*ev(iz*R-ev(R,z)*u0,x)/(x-z)
    assert M0==q**5*j*iz*n*u*((x-V-d)*ev(W,x)+ev(Cq,x))/(x-z)
    fwd=I(Y*u0.subs(Y,C-Y)); rev=I((C-Y)*u0)
    assert S.expand(fwd.subs(Y,C-Y)-ev(rev,C)+rev)==0
for r,s,z,V,B,C,kap,t,q in [
    (2,3,rat(-2,5),rat(2,3),rat(6,7),1,7,rat(3,8),15),
    (rat(-4,3),2,rat(2,5),rat(3,7),rat(4,5),2,-9,rat(-5,11),5),
    (3,-4,rat(7,13),rat(1,3),rat(2,3),3,12,rat(7,8),13),
    (5,8,rat(-5,11),rat(2,7),rat(3,7),5,21,rat(2,3),11)]:
    audit(*map(rat,(r,s,z,V,B,C,kap,t,q)))
print('Exact direct-F1 coordinate checks: signed adjacent tap, affine x, two homogeneous gates, reflected primitive.')
