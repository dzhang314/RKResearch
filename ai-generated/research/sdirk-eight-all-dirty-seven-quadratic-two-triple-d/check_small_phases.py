"""Small exact phase and Vieta residues apart from the two midpoint prefixes."""
from fractions import Fraction as Q
import sympy as S
def L(t,m):return t**4-Q(6,7)*m*m*t*t+Q(3,35)*m**4
m,h=Q(5,3),Q(2,3)
assert L(Q(0),m)-Q(17,9)*L(h,m)==Q(5296,5103)
A,B=Q(4,9),Q(16,9)
assert 35*A*B-21*(A+B)+15==-Q(325,81)
u=S.Symbol('u')
pol=28*u**4-21*u*u+3
g=32*u**4/S.Integer(35)-12*u*u/S.Integer(35)
assert S.rem(g,pol,u)==12*u*u/S.Integer(35)-S.Rational(24,245)
assert S.Poly(g,u).gcd(S.Poly(pol,u)).degree()==0
print('verified exact remaining distinct/shared small phase contradictions')
