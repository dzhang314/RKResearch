#!/usr/bin/env python3
"""Exact scalar and raw triple chronology checks."""
from sympy import Matrix, symbols, cancel
a,c,t,w,v,k,W,nu,lam,x,z,q,H=symbols("a c t w v k W nu lam x z q H")
def eq(lhs,rhs=0): assert cancel(lhs-rhs)==0,(lhs,rhs)
u1,u2=-w*a**2/2,k*a*w-v*a*a/2
g1,g2=-w*a**3/3,k*a*a*w-v*a**3/3
h1,h2=0,k*u1
v1,v2=g1/2+h1,g2/2+h2
eq(v1,-w*a**3/6)
eq(v2,-v*a**3/6)
eq(Matrix([[u1,v1],[u2,v2]]).det(),k*a**4*w*w/6)
# The sum of g-a*u leaves precisely the collided anchor tap if the
# triple weights cancel. The share-wise relation does not identify rows.
p2,p3,k2,k3,w1,w2,w3,z2,z3=symbols("p2 p3 k2 k3 w1 w2 w3 z2 z3")
Weights=Matrix([w1,w2,w3]); K=Matrix([0,k2,k3]); Z=Matrix([0,z2,z3]); d=Matrix([0,1,-1])
U=a*K+c*Z-a**2*Weights/2
G=a*a*K+c*c*Z-a**3*Weights/3
eq(sum(G-a*U),a**3*sum(Weights)/6+c*(c-a)*(z2+z3))
assert (U.subs({k3:-k2,z3:-z2})-(-a**2*Weights/2+(a*k2+c*z2)*d)).applyfunc(cancel)==Matrix([0,0,0])
assert (G.subs({k3:-k2,z3:-z2})-(-a**3*Weights/3+(a*a*k2+c*c*z2)*d)).applyfunc(cancel)==Matrix([0,0,0])
for_fa=nu*a**3+3*a*lam*c**2-2*lam*c**3
eq(for_fa,3*a*(nu*a*a+lam*c*c)-2*(nu*a**3+lam*c**3))
h2=nu*a*a+lam*c*c-t**3/3
h3=nu*a**3+lam*c**3-t**4/4
hu=-nu*a*a/2+a*x+c*z
hh=-a*a*x/2-lam*a*c*c/4
hg=-nu*a**3/3+a*a*x+c*c*z+lam*c*c*(3*a-2*c)/6
eq(-2*for_fa+6*a*h2-4*h3,t**3*(t-2*a))
eq(hu-(a*x+lam*c*c/2)+h2/2,c*z-t**3/6)
eq(hg+2*hh+h3/3,c*c*z-t**4/12)
q=6*a*c-4*(a+c)*t+3*t*t
eq(q.subs(t,2*a),2*a*(2*a-c))
eq(q.subs(t,2*c),2*c*(2*c-a))
print("Exact early defect plane, raw dormant-triple aggregate, and both point resonances verified.")
