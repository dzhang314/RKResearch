"""Exact old-fit coefficients and late-slope projection identity."""
import sympy as S
Y,r,s,c=S.symbols('Y r s c')
c0=s*s*(3*c-4*r)/(r*r-3*s);c1=6*s*(c-r)/r
R=Y**3+c*Y**2+c1*Y+c0
m=Y**2+r*Y+s
z=r*s/(r*r-6*s)
delta=-c*r*r+6*c*s+r**3-7*r*s
Wlead=c*r*r-12*c*s+12*r*s
F=S.QQ.frac_field(r,s,c)
p=lambda a:S.Poly(a,Y,domain=F)
q=S.invert(p(m),p(R))
fit=lambda a:(p(a)*q).rem(p(R))
l=fit(s*Y/2+r*Y**2/3+Y**3/4).nth(1)
rho=fit(s*Y**2/6+r*Y**3/12+Y**4/20)
W=fit(c0*Y/2+c1*Y**2/3+c*Y**3/4+Y**4/5)
same=lambda a,b:S.cancel(a-b)==0
assert same(W.nth(2),(r*r-6*s)*Wlead/(10*(2*r*r-9*s)*delta))
assert same(l.subs(c,-12*r*s/(r*r-12*s)),(r*r-6*s)/(3*(r*r-4*s)))
assert same(delta.subs(c,-12*r*s/(r*r-12*s)),
            r*(r*r-3*s)*(r*r-4*s)/(r*r-12*s))
K=(rho.nth(2)-l-1)/W.nth(2)
x=z-rho.diff().as_expr().subs(Y,z)+K*W.diff().as_expr().subs(Y,z)
eta=S.Rational(6,5)*(1+K)
lin=-z*s+K*c0
V=2*s*(5*r-3*c)*(-18*c*r*r+81*c*s+25*r**3-111*r*s)/(3*(5*r*r-24*s)*Wlead)
assert same(V*eta*c0,x*lin)
assert same((Y-z)*l*(Y-z)-rho.as_expr()+K*W.as_expr(),-(Y-z)*(Y-x))
print('Exact old-fit specialization, zero-W2 guard, and pure V pin verified.')
