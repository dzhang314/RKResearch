#!/usr/bin/env python3
"""Exact polynomial determinant and shifted-Hilbert receipts."""
import sympy as S
Y,a,b,t,s=S.symbols('Y a b t s')
F=lambda y:-3*y*y+4*(a+b)*y-6*a*b
Q=lambda y:2*y-3*a
assert S.expand(F(a)*Q(s)-F(s)*Q(a)+3*a*(s-a)**2)==0
H=lambda y:t*F(y)+12*(y-t)*(t-a)*(t-b)
D=lambda y:t*Q(y)-6*(t-a)*(y-t)
assert S.expand(H(s)*D(t)-H(t)*D(s)+3*t*t*(s-t)**2*(2*t-3*a))==0
print('no prior helper determinant (integer scaled):',S.factor(F(a)*Q(s)-F(s)*Q(a)))
print('one prior helper determinant (integer scaled):',S.factor(H(s)*D(t)-H(t)*D(s)))
G=S.Matrix(5,5,lambda i,j:S.Rational(1,i+j+2))
assert G.det()==S.Rational(1,2**12*3**7*5**5*7**4)
print('shifted Hilbert 5 determinant',G.det())
# Two true moment taps at the first literal singleton.
la=t*t*(3*b-2*t)/(6*a*(b-a))
lb=t*t*(2*t-3*a)/(6*b*(b-a))
assert S.cancel(a*la+b*lb-t*t/2)==0
assert S.cancel(a*a*la+b*b*lb-t**3/3)==0
assert S.cancel(-la*a*a/2+lb*(a*b*(3*b-2*t)/(2*(2*t-3*a))))==0
print('helper Ly, Ly², Lu tap formulas checked')
# First two distinct forward residuals: divided, scaled rows have
# a second divided difference equal to the clock-ratio square.
assert S.expand(s**4-2*s**3+s*s-s*s*(s-1)**2)==0
print('forward residual proportionality forces r²(r−1)²=0')
