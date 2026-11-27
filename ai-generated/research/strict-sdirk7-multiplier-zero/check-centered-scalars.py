#!/usr/bin/env python3
import sympy as S
from fractions import Fraction
from math import isqrt
Y,X,M=S.symbols('Y X M')
a=S.symbols('a:6')
rho=S.Rational(3,5)
R6=X**6+sum(v*X**k for k,v in enumerate(a))
U=X*(X*X-rho);g=X*X-rho
I=lambda F:sum(S.Poly(F,X).nth(j)/S.Integer(j+1) for j in range(0,7,2))
J=lambda F:I(S.cancel((F.subs(X,Y)-F)/(Y-X)))
P=S.Poly(S.expand(U.subs(X,Y)*J(R6)-J(U)*R6.subs(X,Y)+I(R6)*g.subs(X,Y)),Y)
assert J(U)==Y*Y-S.Rational(4,15)
assert P.degree()==2 and P.LC()==S.Rational(4,175)
assert S.rem(P.as_expr()+R6.subs(X,Y)/3,g.subs(X,Y),Y)==0
# Centered multiplier zero at final reflected site e=1 in the reflection suffix.
gphys=(Y-1)**2-rho
Gscaled=Y**3-9*Y**2+18*Y-6
F=Gscaled*(M+2*Y-S.Rational(8,5))+(5*M-4+(4-M)*Y)*gphys
assert S.expand(F-(Y*Y-4*Y+2-M)*(S.Rational(2,5)*(5*Y*Y-19*Y+10)))==0
assert not S.Poly(5*Y*Y-19*Y+10,Y).ground_roots()
print("centered p2 top coefficient, quotient recovery and last-reflection obstruction verified")
