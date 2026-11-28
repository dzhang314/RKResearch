"""Exact symbolic-in-carrier check of the adjacent lead and normalization."""
import sympy as S
Y,U=S.symbols('Y E')
rat=S.Rational
I=lambda f:S.Poly(S.integrate(f,Y),Y).as_expr()
at=lambda f,x:S.expand(f).subs(Y,x)
cf=lambda f,i:S.Poly(f,Y).nth(i)
eq=lambda f,g:S.expand(f-g)==0
def audit(r,s,c,V,h,q):
    c0=s*s*(3*c-4*r)/(r*r-3*s);c1=6*s*(c-r)/r
    R=Y**3+c*Y**2+c1*Y+c0
    m=h*(Y**2+r*Y+s)
    n=S.resultant(m,R,Y)
    mi=S.invert(m,R,Y)
    fit=lambda g:S.rem(mi*g,R,Y)
    P=Y*m;P0=Y*R
    el,rho,W=map(fit,(I(P)/Y,I(I(P))/Y,I(P0)/Y))
    z=r*s/(r*r-6*s);p=q*z;Z=q*Y-p
    l=cf(el,1);delta=h*(rat(1,4)-l)
    F,rem=S.div(W,Y-z,Y);assert eq(rem,0)
    B0,rem=S.div(I(P0)-P*W,P0,Y);assert eq(rem,0)
    K=U/q
    Q4=Z*P+U*P0
    Lh=n*(Z*el-q*rho+U*W)
    xN=-(q*cf(Lh,1)+p*cf(Lh,2))
    etaN=(n*q/5-cf(Lh,2))*cf(Q4,4)
    Af=q*etaN*V*c0+xN*cf(Q4,1)
    dv=at(B0,V)-K*at(F,V)
    A=(V-z)*(delta-l*K)+((1+l)*K-delta)*dv
    assert eq(Af,n*q**3*c0*A/(1+l))
    assert S.Poly(Af,U).nth(2)==-c0*q*n*at(F,V)
for row in [(2,3,5,rat(2,3),7,11),(-4,7,9,rat(3,7),-5,8),
            (5,-4,7,rat(1,3),12,13),(3,1,-2,rat(2,7),16,31)]:
    audit(*map(rat,row))
print('Four QQ symbolic-carrier probes verify the exact adjacent leading coefficient and scale.')
