#!/usr/bin/env python3
"""Exact rational prime support for the two-live-zero forward/retrospective gates."""
from sympy import QQ,CRootOf,Symbol,ring

t=Symbol('X')
p=70*t**4-140*t**3+90*t*t-20*t+1
x0=CRootOf(p,0);x1=CRootOf(p,1)
K=QQ.algebraic_field(x0,x1)
a=K.from_sympy(x0);b=K.from_sympy(x1)
o=K.one
R,x=ring('T',QQ)
def as_poly(b):return sum((R(c)*x**j for j,c in enumerate(b.to_list()[::-1])),start=R.zero)
minp=sum((R(c)*x**j for j,c in enumerate(K.mod.to_list()[::-1])),start=R.zero)
def normnum(w):
    y=minp.resultant(as_poly(w))
    return abs(int(y.numerator))
