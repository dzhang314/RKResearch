#!/usr/bin/env python3
"""Exact two-common-clock obstruction for the paid fifth primitive."""
from functools import reduce
import sympy as S
X,B=S.symbols('X B')
J4=lambda x:42*x**4-84*x**3+56*x*x-14*x+1
J5=lambda x:(2*x-1)*(66*x**4-132*x**3+84*x*x-18*x+1)
assert S.Poly(S.gcd(J4(X),J5(X)),X,domain=S.QQ).is_one
def integ(q):
    p=S.Poly(q,X)
    return sum(v/S.Integer(i+1) for (i,),v in p.terms())
assert S.Matrix(4,4,lambda i,j:S.Rational(1,(i+j+2)*(i+j+3))).det()!=0
assert all(integ(X**(i+1)*(1-X)*P(X))==0 for P in (J4,J5) for i in range(4))
F,rem=S.div(J5(X)*J4(B)-J4(X)*J5(B),X-B,X)
assert rem==0
L=S.Add(*(v*X**i/S.Integer(i+1) for (i,),v in S.Poly(X*F,X).terms()))
Q,rem=S.div(L*J4(B)-L.subs(X,B)*J4(X),X-B,X)
assert rem==0
f,g=[S.Poly(k,X,domain=S.QQ[B]) for k in (F,Q)]
assert f.degree()==g.degree()==4
assert S.expand(f.LC()-132*J4(B))==0 and S.expand(g.LC()-22*J4(B)**2)==0
res=S.Poly(f.resultant(g),B,domain=S.QQ)
for degree in (3,2,1):
    h,r=f.pdiv(g)
    assert f*g.LC()**(f.degree()-g.degree()+1)==h*g+r
    assert r.degree()==degree
    f,g=g,r
d=reduce(S.gcd,(res,*[S.Poly(a,B,domain=S.QQ) for a in g.all_coeffs()]))
goal=S.Poly((B-1)**4*J4(B)**4,B,domain=S.QQ)
assert d.monic()==goal.monic()
print("Jacobi fifth quotient: exact resultant/pseudoremainder gcd supported only on B=1 or J4(B)=0")
