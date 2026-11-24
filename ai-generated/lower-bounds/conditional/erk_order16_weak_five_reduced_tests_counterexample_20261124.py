#!/usr/bin/env python3
"""Exact, small check of the new scalar negative control, not an RK replay."""
from fractions import Fraction as Q
from hashlib import sha256
from math import factorial
from pathlib import Path
import json
import sys

u, z = Q(2, 3), Q(1, 3)
a_lo, a_hi = Q(9, 16), Q(37, 64)
h_lo, h_hi = 1-a_hi, 1-a_lo
q = (82, -1020, 3855, -5670, 2835)
H = (-41, 258, -480, 270)

def evaluate(coeff, x):
    return sum(c*x**j for j,c in enumerate(coeff))

def product(a,b):
    c=[Q(0)]*(len(a)+len(b)-1)
    for i,ai in enumerate(a):
        for j,bj in enumerate(b):
            c[i+j] += ai*bj
    return c

# F' divided by x(x-u) must equal q.
Hp = tuple(j*c for j,c in enumerate(H) if j)
assert tuple(Q(3,2)*(a+b) for a,b in zip(product((-2*u,4),H),
                                       product((0,-u,1),Hp))) == tuple(map(Q,q))
assert [sum(c*u**(i+k+1)/Q(i+k+1) for i,c in enumerate(q)) for k in (1,2)] == [0,0]
assert evaluate(H,a_lo) == Q(623,2048)
assert evaluate(H,a_hi) == -Q(13429,131072)
assert evaluate(H,h_hi) == Q(5345,2048)
assert evaluate(Hp,a_lo) == -Q(3291,128)
assert evaluate(Hp,h_lo) == -Q(5811,2048)
assert max(a_hi,h_hi)<Q(16,27) # H''<0 over both brackets
assert 0<z<h_lo<h_hi<a_lo<a_hi<u<1
assert evaluate(q,u)==evaluate(q,z)==-Q(14,3)
print('Exact endpoint arithmetic and primitive factor at the isolated root: pass')

numerators = (1,26,44,54,64,74,84,94,110)
if len(sys.argv)>1:
    raw=Path(sys.argv[1]).read_bytes()
    assert sha256(raw).hexdigest()=='1f4288ab97bbc01cbc3c47b14d18355c0157d5c7fbcba23acc50bf03ae72104e'
    data=json.loads(raw)
    assert data['node_denominator']==128
    assert set(numerators)<=set(data['node_numerators'])
    print('Audited rule hash and sample-node membership: pass (not a weight replay)')

def sign(x):
    return (x>0)-(x<0)

def side(x, lo, hi):
    if lo==hi:
        return sign(x-lo)
    assert x<=lo or hi<=x
    return -1 if x<=lo else 1

observed=[]
observed_factors=[]
for n in numerators:
    x=Q(n,128)
    N=side(x,u,u)*side(x,z,z)*side(x,a_lo,a_hi)*side(x,h_lo,h_hi)
    S=sign(evaluate(q,x))
    observed.append(S*N)
    observed_factors.append((S,N))
assert observed_factors==[(1,1),(-1,1),(-1,-1),(1,-1),(1,1),(1,-1),(-1,-1),(-1,1),(1,1)]
assert observed==[1,-1,1,-1,1,-1,1,-1,1]
print('Sign witness at n/128, n =', *numerators)
print('Signs of qN4:', *('+' if x>0 else '-' for x in observed))

beta=lambda k:Q(factorial(k)**2,factorial(2*k+1))
m=lambda k:2835*beta(k+2)-1020*beta(k+1)+82*beta(k)
assert (m(1),m(2),m(3))==(-Q(1,12),-Q(11,210),-Q(7,660))
nu=u*(1-u)
assert (nu*m(1)-m(2),m(3)-nu*m(2))==(Q(32,945),Q(43,41580))
print('Omitted global I(1) = (32/945) a(1−a) + 43/41580 > 0: pass')
