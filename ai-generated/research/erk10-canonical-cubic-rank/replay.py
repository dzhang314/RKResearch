#!/usr/bin/env python3
"""Exact scalar receipts for the canonical six-opening cubic rank gates."""
from sympy import Matrix, symbols, cancel
e,p,q,r,a,b=symbols("e p q r a b")
s=2*p/3
def eq(lhs,rhs=0):assert cancel(lhs-rhs)==0,(lhs,rhs)
xe=-e**2/2
eq((s**2/(2*e))*xe,-e*s**2/4)
vp=3*p/4
vq=(p*q**2/2-q**3/3)/(s*(p-s))
eq(vq,3*q*q*(3*p-2*q)/(4*p*p))
qp=vp*s**3-p**4/4
eq(qp,-p**4/36)
tap_p=(q**3/3-s*q**2/2)/(p*(p-s))
qq=vq*s**3+tap_p*p**3-q**4/4
eq(qq,5*p*q**3/9-p*p*q*q/3-q**4/4)
eq(qp*vq-qq*vp,3*p*q*q*(p-q)**2/16)
j=lambda x:[x**k/k for k in range(2,5)]
v=lambda x:[x**k for k in range(1,4)]
eq(Matrix([j(a),v(a),j(b)]).det(),a**4*b*b*(a-b)**2/24)
eq(Matrix([j(a)[:2],v(a)[:2]]).det(),a**4/6)
J=lambda x:[x**(k+3)/(k+3)-r*x**(k+2)/(k+2)for k in range(2)]
eq(Matrix([J(a),J(r)]).det(),a*a*r**3*(a-r)**2/24)
print("Four independent old-pure pivots and exact point/generic first-two-high minors replayed.")
