#!/usr/bin/env python3
"""Pressure divisor for an actual 15-row trial, first reverse a=2/5."""
from sympy import symbols, Rational as Q, expand, Poly, cancel,factor,prod
from pathlib import Path
import json
x,D,E=symbols('x D E')
A,C=Q(3,5),Q(2,5)
Y=[A,C,D,E]
a,t,d=1-A,1-C,1-D
L=Poly(x*(1-x)*prod(x-y for y in Y),x)
mu=[sum(c/(j+m[0]+1)for m,c in L.terms())for j in range(4)]
det=expand(mu[0]*mu[2]-mu[1]*mu[1])
S=expand(mu[0]*mu[3]-mu[1]*mu[2]);P=expand(mu[1]*mu[3]-mu[2]*mu[2])
quad=det*x*x-S*x+P
H=[]
for n,o in enumerate(Y):
    F=Poly(x*(x-1)*quad*prod(x-y for j,y in enumerate(Y)if j!=n),x)
    H.append(cancel(sum(c/(m[0]+1)for m,c in F.terms())/(o-1)))

fixed=lambda y:(a+t)*y**3/3-a*t*y*y/2-y**4/4
B0=[H[i]*fixed(1-o)for i,o in enumerate(Y[:3])]
dd=[1/prod(u-v for v in Y[:3] if v!=u)for u in Y[:3]]
Rden=cancel(sum(k*w for k,w in zip(B0,dd)))
Rnum=cancel(sum(k*w*z for k,w,z in zip(B0,dd,Y)))
# Scale the projected abstract k4 pressure by both common denominators.
Z=[cancel(h*(u*Rden-Rnum))for h,u in zip(H,Y)]
coeff=[cancel(Z[i]*fixed(1-u))for i,u in enumerate(Y[:3])]
pE=cancel(coeff[0]+(E-A)*(coeff[1]-coeff[0])/(C-A))
early4=lambda y:(a*a+a*t+t*t)*y**3/3-a*t*(a+t)*y*y/2-y**5/5
e=1-E
late4=(a+t+d)*e**4/4-(a*t+a*d+t*d)*e**3/3+a*t*d*e*e/2-e**5/5
T=[early4(1-y)*zz for y,zz in zip(Y[:3],Z)]+[late4*Z[3]+(a+t+d)*pE]
top=cancel(sum(n/prod(y-v for v in Y if y!=v)for n,y in zip(T,Y)))


pr=Poly(factor(top).as_numer_denom()[0],D,E)
print('degrees',pr.degree(D),pr.degree(E),'termcount',len(pr.terms()))
