#!/usr/bin/env python3
"""Independent first-three scalar identities, over the rational function field."""
from sympy import Matrix, symbols, cancel
a=symbols('a')
b=2*a-1
f=-2*(a-1)*(3*a-5)/(a**3-7*a**2+10*a-2)
A=Matrix([[1,0,0],[a-1,1,0],[b-1-f,f,1]])
c=Matrix([1,a,b]);C=Matrix.diag(*c)
cp=lambda k:Matrix([x**k for x in c])
g=A*c-cp(2)/2
eta=2*g[1];d=A*cp(2)-cp(3)/3
G=A*g-g-(C*g-g)/eta
H=d-(A*g+C*g)*2/3
assert all(cancel(x)==0 for x in [*G,*H])
print('AP shifted primitive and degree-three defect identities verified over Q(a).')
