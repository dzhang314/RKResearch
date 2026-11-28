#!/usr/bin/env python3
"""Exact independent scalar identities and complete small slot enumeration."""
import sympy as S
x=S.symbols('x')
J4=42*x**4-84*x**3+56*x**2-14*x+1
omega=x*(1-x)
assert S.integrate(omega*J4**2,(x,0,1))==S.Rational(1,330)
assert all(S.integrate(omega*J4*x**k,(x,0,1))==0 for k in range(4))
Gram=lambda w:S.Matrix([[S.integrate(w*x**(i+j),(x,0,1))for i in range(5)]for j in range(5)])
assert Gram(x).det()!=0 and Gram(omega).det()!=0
print('Fixed rational terminal/ordinary Gram and Jacobi integrals verified.')

a,b,c,d,t=S.symbols('a b c d t')
Q=lambda z:(z-b)*(z-c)*(z-d)
assert S.expand(Q(a)-(a**3-(b+c+d)*a**2+(b*c+b*d+c*d)*a-b*c*d))==0
assert all(S.expand(Q(z))==0 for z in (b,c,d))
b0,b1,h0,h1,g0,g1,G0,G1=S.symbols('b0 b1 h0 h1 g0 g1 G0 G1')
h=b0*h0+b1*h1
sq=b0*h0**2+b1*h1**2
assert S.expand(sq+h0*h1*(b0+b1)-(h0+h1)*h)==0
assert S.expand(sq-b0*h0*(h0-h1)-h1*h)==0
g=G0*g0+G1*g1
gg=G0*g0**2+G1*g1**2
gh=G0*g0*h0+G1*g1*h1
assert S.expand(gg-g1*g-G0*g0*(g0-g1))==0
assert S.expand(g0*g-gg-G1*g1*(g0-g1))==0
assert S.expand(g.subs(g1,g0)-g0*(G0+G1))==0
assert S.expand(gh.subs(g1,g0)-g0*(G0*h0+G1*h1))==0
print('Both unequal/equal dirty reads, pair masses, and four-label separator verified.')

# o is the origin marker (0/1), i the live nonendpoint markers, f
# the nonendpoint zero-mass markers. q counts nonzero square masses.
survive={(z,i,o,f,i+o+f) for z in range(1,7) for i in range(6)
         for o in (0,1) for f in range(7)
         if i+o+f>=4 and 7+z+i+2*o+3*f<=13}
assert survive=={(1,4,0,0,4),(1,5,0,0,5),(1,3,1,0,4),(2,4,0,0,4)}
print('All and only slot possibilities before the rank test:',sorted(survive))

# C2 and zero cubic at first clock beyond 0,xi, needed for h live.
xi,u,d,Tap=S.symbols('xi u diag tap')
old=xi*Tap+u*d-u*u/2
new=xi**2*Tap+u*u*d-u**3/3
assert S.expand(u*old-new-(xi*(u-xi)*Tap-u**3/6))==0
print('First off-core literal two-moment debit verified.')
