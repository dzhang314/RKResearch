#!/usr/bin/env python3
"""Unconditional front/rear characteristic incompatibility for four ordinary sites."""
from sympy import symbols, Poly, div, expand, integrate, resultant
from math import gcd,prod
u,x,y,T=symbols('u x y T')
Q=4*u**3-12*u**2+3*u+2
def L(x):return 70*x**4-140*x**3+90*x*x-20*x+1
D,r=div(L(y)-L(x),y-x,y)
assert r==0
R=(T-1)*(T-1-u)*(T-1-2*u)
J=integrate(R,(T,0,T))
G=Poly(expand(12*(J-R)),T)
F=expand(sum(G.nth(k)*y**k*x**(4-k) for k in range(5)))
A=resultant(resultant(L(x),L((1+2*u)*x),x),Q,u)
B0=resultant(G.eval(1),Q,u)
B1=resultant(resultant(resultant(D,F,y),L(x),x),Q,u)
assert A==2**57*5**12*7**6*3517*10759456151
assert B0==-2**6*3**5
assert B1==2**112*3**45*5**48*7**25*853*9453064485587*77302364448451*12847924825634167528081
rear=prod((37,269,379,397,487,69877))
assert rear==50962055131435661
assert [gcd(rear,int(n)) for n in (A,B0,B1)]==[1,1,1]
for title,m in zip(('Gaussian first physical zero','coincident Gaussian live clock','distinct Gaussian live clock'),(A,B0,B1)):
    print(title,'norm',m,'gcd with rear support',gcd(rear,int(m)))
