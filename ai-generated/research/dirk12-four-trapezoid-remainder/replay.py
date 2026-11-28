#!/usr/bin/env python3
"""Exact AP13 census and individual weighted cubic remainder checks."""
from fractions import Fraction as Q
from math import factorial, gcd, lcm, prod
from itertools import combinations
from collections import Counter
def pprod(xs):
    p=[Q(1)]
    for t in xs:p=[-t*p[0]]+[a-t*b for a,b in zip(p,p[1:])]+[p[-1]]
    return p
def inte(p):
    return sum(a/(i+1) for i,a in enumerate(p))
def v(p,x):
    z=0
    for a in reversed(p):z=z*x+a
    return z
def mul(p,q):
    z=[Q(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):z[i+j]+=a*b
    return z
def strip(a):
    if not a:return 0
    while (g:=gcd(a,factorial(12)))>1:a//=g
    return abs(a)
def unit(a):
    a=Q(a)
    return strip(a.numerator)==strip(a.denominator)==1
J=(0,-1,20,-120,300,-330,132)
w0=(Q(0),Q(1),Q(-3),Q(3),Q(-1)) # X(1-X)^3
z=Q(1,2)
count=0
Rs=[]
for m in range(2,13,2):
    for e in range(m-12,1):
        P=tuple(Q(j,m) for j in range(e,e+13) if j not in (0,m))
        for H in combinations([r for r in P if r!=z],4):
            C=tuple(r for r in P if r not in H)
            if not any(unit(v(J,r)) for r in C):continue
            count+=1
            f=inte(mul(w0,pprod(C)))
            if not f:Rs.append((m,e,H,C))
assert count==4221 and len(Rs)==2
print("qualified exact candidates",count,"four-trapezoid resonances",len(Rs))
for m,e,H,C in Rs:
    Delta=[]
    for x in C:
        others=[t for t in C if t!=x]
        L=pprod(others)
        Delta.append(-inte(mul(w0,L))/(6*x*prod(x-t for t in others)))
    assert all(sum(f*x**j for f,x in zip(Delta,C,strict=True))==
               Q(-1,prod(j+d for d in range(1,5))) for j in range(1,9))
    D=lcm(*(q.denominator for q in Delta))
    assert strip(D)==1
    print("grid",m,e,"traps",tuple(map(str,H)),"seven remainder sites",tuple(map(str,C)))
    print("remainder unit delta clocks",tuple(str(x) for x,u in zip(C,Delta,strict=True) if unit(u)))
    print("integer index, scaled delta, denominator:",
          list(zip([int(x*m) for x in C],[int(x*D) for x in Delta],strict=True)), D)
print("quadrature and eight paid cubic tests verified for both exact remainders")
