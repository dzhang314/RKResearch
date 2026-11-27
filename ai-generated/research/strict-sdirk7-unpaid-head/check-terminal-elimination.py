#!/usr/bin/env python3
"""Replay the exact reverse-stage elimination over Q, without solving a Cramer system."""
from sympy import symbols, Rational as Q, resultant, factor, cancel, prod
u,v,d,t,c,e = symbols("u v d t c e")
L=lambda x:x*x/2-2*x+1
theta=1/(2*L(u))
f=lambda x:-Q(4,3)+(2*theta-2)*(x-1)/3
r=v-1-t
eq1=d-v*v/2+v+t*u+r
eq2=v*v+t*u*u+r-v**3/3-f(v)*d
eq3=t*L(u)-r/2-theta*(1-v)*d
ans=factor(resultant(resultant(eq1,eq2,t),resultant(eq1,eq3,t),d))
want=(u-1)**2*(u-v)*(v-1)*(u+v-4)*(2*u-v-1)/(3*(u*u-4*u+2))
assert cancel(ans-want)==0
print("Cramer-safe elimination:", ans)
T0=c-1
T1=c*c/2-c-e
T2=c**3/3-c*c+(-1-c/3)*e
res=T2/2-2*T1+T0-Q(1,2)*(1-c)*e
want=(2*(c+3)*e+c**3-9*c*c+18*c-6)/6
assert cancel(res-want)==0
print("Fourth reverse row at u=0:", factor(res))
