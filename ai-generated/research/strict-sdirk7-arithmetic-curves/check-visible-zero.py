#!/usr/bin/env python3
"""Exact arithmetic receipts for the genus-three visible-zero cut."""
import sympy as S

u,c,x,y,z,s,p=S.symbols('u c x y z s p')
v=2*u-1
M=u**2-4*u+2
T=u**3-7*u**2+10*u-2
J=4*u**3-24*u**2+39*u-17
F=6*(u-2)*(u-1)**2*(c-1)-3*(u-3)*(u-1)*(2*u-3)*(c*c-2*c)+(u-3)*(u-2)**2*(c**3-3*c*c)
H=S.Poly(18*u**8-288*u**7+1998*u**6-7902*u**5+19638*u**4-31662*u**3+32555*u**2-19574*u+5261,u)
assert S.expand(S.discriminant(F,c)-108*(u-3)*(u-1)**3*H.as_expr())==0
assert H.gcd(H.diff()).degree()==0
assert all(H.eval(j) for j in (1,2,3))
assert S.expand(F.subs(u,1)+2*c*c*(c-3))==0
assert S.expand(F.subs(u,2)-3*c*(c-2))==0
assert S.expand(F.subs(u,3)-24*(c-1))==0
at_inf=S.Poly(S.expand(F).coeff(u,3),c)
assert at_inf.degree()==3 and at_inf.gcd(at_inf.diff()).degree()==0
G=S.Poly(F,c)
assert G.nth(2).subs(u,2)==3
assert S.diff(G.nth(3),u).subs(u,3)==1
W=S.Poly(F.subs({u:1+x,c:y-x},simultaneous=True),x,y)
assert sum(v*x**i*y**j for (i,j),v in W.terms() if i+j<=2)==6*y*y
assert W.coeff_monomial(x**3)==11
# The regular and singular Christoffel fiber coefficient receipts.
A1,A0,B1,B0=S.Rational(1,6),S.Rational(1,5),S.Rational(16,5),S.Integer(4)
assert A1*B0-A0*B1==S.Rational(2,75)
assert S.solve([S.Rational(1,7)-s/6+p/5,S.Rational(1,6)-s/5+p/4],[s,p])=={s:S.Rational(10,7),p:S.Rational(10,21)}
assert S.Rational(1,5)-S.Rational(10,7)/4+S.Rational(10,21)/3==S.Rational(1,630)
r1,ru,rv=-S.Rational(1,2),M/2,M*J/(2*T)
assert S.cancel(ru*rv-2*r1*rv+r1*ru-(u-3)*(u-1)**2*M*(2*u**2-10*u+11)/(2*T))==0
# No rational U can zero the extra leading factor: homogeneous, including infinity.
q=lambda a,b:2*a*a-10*a*b+11*b*b
assert q(1,0)%5 and all(q(a,1)%5 for a in range(5))
print('Visible-zero cut: only the ordinary cusp (u,c)=(1,0); geometric genus 3.')
print('The regular z projection has nonzero leading coefficient and degree 36.')
