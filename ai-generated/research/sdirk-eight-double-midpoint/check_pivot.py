#!/usr/bin/env python3
"""Exact replay of the two uniform midpoint prefixes and the first-clock pivot."""
import sympy as s
m,t=s.symbols('m t')
b=3-m
Z=18*m*m-126*m+203
U=lambda t:(t-b)*((t-b)**2-4)*(t+3*b)
assert s.expand(U(t)-(t**4+(-6*b*b-4)*t*t+(8*b**3-8*b)*t-3*b**4+12*b*b))==0
assert s.expand(-7*(6*m*m/7-6*b*b-4)/2-Z)==0
A=-16*b*(b*b-1)
B=4*(3*m**4/35+3*b**4-12*b*b)
D=2*b*(b*b-4)
E=6*b
F=-4*(3*m*m/5+3*b*b-4)
w=(1-m)**2
assert s.gcd(s.Poly(Z,m),s.Poly(b*(b*b-1),m)).degree()==0
P=t*t*t-3*m*m*t/5-((D+E*t*t)/2+F*t/4)
assert s.expand(P-(t-b)*((t-b)**2-4))==0
Q=B*(D+E*w)-F*A*w
quo=16*(1296*m**5-10044*m**4+30384*m**3-43056*m*m+33131*m+4081)/7
assert s.expand(405*Q-(2274704*m-5703824)-quo*Z)==0
assert s.gcd(s.Poly(Z,m),s.Poly(2274704*m-5703824,m)).degree()==0
print('double-midpoint: nonzero first-clock residual pivot in the forced quadratic field')
