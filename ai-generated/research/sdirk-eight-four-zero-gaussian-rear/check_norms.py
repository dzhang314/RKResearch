#!/usr/bin/env python3
"""Guarded integer resultants for the four-zero Gaussian rear cases."""
from sympy import symbols, expand, Poly, div, resultant
from math import isqrt
x,y,z,v=symbols('x y z v')
def L(f):return 70*f**4-140*f**3+90*f**2-20*f+1
def D(f):
    q,r=div(L(f)-L(x),f-x,f)
    assert r==0
    return q
def B(f):
    q,r=div(D(z)-D(y),z-y,z)
    assert r==0
    return expand(q.subs(z,f))
def norm(g):return abs(int(resultant(L(x),resultant(D(y),g,y),x)))
h=y-x
N0=[norm(-2*x**3+h*x*x+4*x*h*h-h**3),norm(B(2*y-x)),norm(B(4*x-y))]
assert N0==[
    2**17*5**13*7**6*397*487*69877,
    2**30*3**6*5**24*7**16,
    2**30*5**20*7**16*37**2*269**2*379**2]
n1=[]
for num in [1+2*v,3-v]:
    p=Poly(D(y),y)
    K=expand(sum(p.nth(j)*(x*num)**j*(1+v)**(3-j) for j in range(4)))
    n1.append(abs(int(resultant(v*v-2*v-1,resultant(L(x),K,x),v))))
assert n1==[2**8*5**8*7**5*17*103*7793,2**30*5**8*7**4*13**2*131**2]
for p in (397,487,69877,37,269,379,17,103,7793,13,131):
    assert all(p%d for d in range(2,isqrt(p)+1))
print('n=0 ghost/arithmetic/star norms',N0)
print('n=1 canceled arithmetic/star norms',n1)
