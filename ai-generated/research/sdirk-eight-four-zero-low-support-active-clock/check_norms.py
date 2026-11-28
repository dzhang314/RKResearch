#!/usr/bin/env python3
"""Exact projection of the two consecutive reverse zero reads."""
from sympy import symbols, Rational as R, integrate, expand, Poly, rem, resultant, numer, denom
from math import isqrt
v,t,y,z=symbols("v t y z")
q=v**3-3*v**2+R(3,4)*v+R(1,2)
l=y**4-R(6,7)*y**2+R(3,35)
p=1+(2-v)*(t-1)
r=(t-1)*(t-1-v)
j=lambda f:integrate(f,(t,0,t))
b=1+2*v
gate=rem(expand(r.subs(t,b)*(j(p)-p)-p.subs(t,b)*(j(r)-r)),q,v)
G=(2*v**2-4*v-1)*t**3+(-18*v**2+30*v+9)*t**2+(48*v**2-60*v-21)*t-24*v**2+24*v+9
assert expand(3*gate-G)==0
assert expand(G.subs(t,b)-8*(2*v**2-4*v-1)*q)==0
def paid(f):
    for c in Poly(f,v,t,y,z).coeffs():
        d=int(denom(c))
        for p in (2,3,5,7):
            while d%p==0:d//=p
        assert d==1
h=Poly(gate,t)
s=expand(sum(h.nth(i)*(1+y)**(3-i)*((1+z)*b)**i for i in range(4)))
s=rem(s,q,v)
paid(s)
for mode in ('mirror','other'):
    w=rem(s.subs(z,-y),l,y) if mode=='mirror' else rem(resultant(s,z*z+y*y-R(6,7),z),l,y)
    w=rem(w,q,v)
    x=rem(resultant(w,l,y),q,v)
    n=resultant(x,q,v)
    for f in (w,x,n):paid(f)
    if mode=='mirror':
        assert int(numer(n))==-2**34*3**7*1265639
        assert int(denom(n))==5**9*7**9
    else:
        assert int(numer(n))==2**80*3**14*1174307*263949107
        assert int(denom(n))==5**18*7**36
    print(mode,'norm =',n)
for p in (1265639,1174307,263949107):
    assert all(p%d for d in range(2,isqrt(p)+1))
    print('certified prime by trial division:',p)
