"""Exact old-profile coefficient and factor ledger for this contact."""
import sympy as S
r,s,c2=S.symbols('r s c2')
c0=s*s*(3*c2-4*r)/(r*r-3*s)
c1=6*s*(c2-r)/r
z=r*s/(r*r-6*s)
D=-c2*r*r+6*c2*s+r**3-7*r*s
Rz=z**3+c2*z*z+c1*z+c0
rhs=-s*s*(2*r*r-9*s)*(5*r*r-24*s)*D/((r*r-6*s)**3*(r*r-3*s))
assert S.cancel(Rz-rhs)==0
fix=lambda expr:S.cancel(expr.subs(s,5*r*r/24))
assert fix(5*r*r-5*c2*r+4*c1)==0
assert fix(100*r**3-75*c2*r*r+216*c0)==0
assert fix(z+5*r/6)==0
print('Exact direct-Fn old clock contact factor and reconstructed equations verified.')
