"""Exact symbolic direct-Fn identities for the two extra small contacts."""
import sympy as S
Y,r,s,c2=S.symbols('Y r s c2')
c0=s*s*(3*c2-4*r)/(r*r-3*s)
c1=6*s*(c2-r)/r
R=Y**3+c2*Y**2+c1*Y+c0
m=Y**2+r*Y+s
P=Y*m; P0=Y*R
I=lambda f:S.integrate(f,Y).expand()
K=S.QQ.frac_field(r,s,c2)
F=lambda f:S.Poly(f,Y,domain=K)
mp=S.invert(F(m),F(R))
fit=lambda f:S.rem(F(f)*mp,F(R)).as_expr()
ell=fit(I(P)/Y); rho=fit(I(I(P))/Y); W=fit(I(P0)/Y)
p=r*c0; q=3*s*c2-4*r*s-3*c0
z=r*s/(r*r-6*s)
D=-c2*r*r+6*c2*s+r**3-7*r*s
lc=S.Poly(ell,Y).nth(1)
ok=lambda a,b: S.cancel(a-b)==0
assert ok(p,z*q) and ok(q,s*(3*c2-4*r)*(r*r-6*s)/(r*r-3*s))
assert ok(S.resultant(F(m),F(R)), -s*s*(2*r*r-9*s)*D**2/(r*r*(r*r-3*s)**2))
assert ok(S.diff(rho,Y).subs(Y,z),
          r*s*(2*r-c2)*(r*r-3*s)/(20*(2*r*r-9*s)*D))
assert ok(S.diff(W,Y).subs(Y,z),
          -s*(2*r-c2)*(-15*c2*r*r+90*c2*s+16*r**3-108*r*s)/(20*(2*r*r-9*s)*D))
assert all(ok(a.subs(Y,z),0)for a in (ell,rho,W))
k=z*s/c0
u=-(3*c2-4*r)*(r*r-6*s)
g=S.Poly((Y-z)*m+k*R,Y)
assert all(ok(g.nth(i),v*D/u)for i,v in enumerate((0,6*s,4*r,3)))
g=S.Poly((Y-z)*m-R,Y)
assert ok(g.nth(1),6*s*D/(r*(r*r-6*s)))
assert ok(g.nth(2),D/(r*r-6*s))
print('Independent exact fraction-field old-fit, determinant and monomial checks passed.')
