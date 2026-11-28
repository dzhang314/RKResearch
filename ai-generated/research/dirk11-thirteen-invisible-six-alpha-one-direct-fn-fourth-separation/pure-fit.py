"""Exact old polynomial affinity and numerator certificate."""
import sympy as S
Y,r,s,c2=S.symbols('Y r s c2')
c0=s*s*(3*c2-4*r)/(r*r-3*s)
c1=6*s*(c2-r)/r
R=Y**3+c2*Y**2+c1*Y+c0
m=Y**2+r*Y+s
P=Y*m
P0=Y*R
z=r*s/(r*r-6*s)
I=lambda f:S.integrate(f,Y).expand()
K=S.QQ.frac_field(r,s,c2)
F=lambda f:S.Poly(f,Y,domain=K)
mi=S.invert(F(m),F(R))
fit=lambda f:(F(f)*mi).rem(F(R)).as_expr()
ell=fit(I(P)/Y)
w=fit(I(P0)/Y)
l=F(ell).nth(1)
delta=S.Rational(1,4)-l
p4,rr=F(w).div(F(Y-z))
assert rr.is_zero
b0,rr=F(I(P0)-P*w).div(F(P0))
assert rr.is_zero
assert F(delta*p4.as_expr()-l*b0.as_expr())==F(-(1+l)*(r*r-6*s)*Y/(10*(2*r*r-9*s)))
print('Exact affine polynomial identity over Q(r,s,c₂) verified.')
