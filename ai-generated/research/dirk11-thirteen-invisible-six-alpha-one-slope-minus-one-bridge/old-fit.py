"""Exact integer polynomial identity and independent old quotient check."""
import sympy as S
Y,r,s,z=S.symbols('Y r s z')
m=Y**2+r*Y+s
R=15*Y**3+(16*r-12*z)*Y**2+(18*s-12*z*r)*Y-12*z*s
D=2*r*r-9*s
Q=(-9*r*r+48*s)*Y**2+(8*r*r*z+3*r*s-42*s*z)*Y-2*r*s*z
T=10*s*Y**2+5*r*Y**3+3*Y**4
assert S.expand(D*T-6*m*Q-R*((4*r*r-21*s)*Y-r*s))==0
assert S.expand(Q.subs(Y,z)+z*((r*r-6*s)*z-r*s))==0
assert S.expand(m.subs(Y,-2*r/3)+D/9)==0
assert S.expand(R.subs(Y,-2*r/3)-4*(r+z)*D/3)==0
assert S.expand(5*(r*((18*s-12*z*r)/15+6*s)-6*(16*r-12*z)*s/15)-4*(r*s-z*(r*r-6*s)))==0
K=S.QQ.frac_field(r,s,z)
p=lambda a:S.Poly(a,Y,domain=K)
mi=S.invert(p(m),p(R))
assert (p(T/60)*mi).rem(p(R))==p(Q/(10*D))
c0=-64*r**3/405;c1=-8*r*r/9
assert S.expand(225*c0*c0+8*c1**3)==0
print('The integer primitive certificate, old rational fit, and lost-ratio scalar identity agree.')
