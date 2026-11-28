#!/usr/bin/env python3
"""Exact homogeneous equal-defect and third dirty row moment arithmetic."""
import sympy as S
Q=S.Rational
r,e,J=S.symbols("r e J")
T=3*r*(r-1)*J
U=-r*(3*r-2)*J
h3=(3-2*r)*(U+r*r*(3-2*r)*J)-2*(e-1)*T
h4=(3-2*r)*(U+r**3*J)+(3-2*r+(r-1)*(e-1))*T/2
assert S.factor(h3)==2*J*r*(r-1)*(-3*e+2*r*r-r)
expect=J*r*r*(r-2)*(r-1)*(2*r-3)/2
assert S.cancel(h4.subs(e,r*(2*r-1)/3)-expect)==0
print("equal defect fifth row: final constraint",S.factor(expect))
x,y=S.symbols("x y")
z=Q(-1,2);p=Q(3,2)
V3=z*(y-z)
v=z/y*x*(x-z)
moment1=Q(1,2)+x
moment2=Q(1,3)+(Q(2,3))*x-(Q(2,3))*v
H=S.factor((moment2-moment1)/(p*p-p))
sigma=S.factor(moment1-p*H)
a=S.factor((v-z*sigma)/(y-z))
W=S.factor(a*V3)
G=S.factor(sigma+p**3*H-Q(1,4))
assert S.factor(G-x/2+v-W/2)==(x-y)*(2*x+1)/(16*y)
for d in [z,y]:
    assert H.subs(x,d)==a.subs(x,d)==0
    assert S.cancel(sigma.subs(x,d)-(d-z))==0
print("third dirty row: G−d/2+V−W/2 =",S.factor(G-x/2+v-W/2))
