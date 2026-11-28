#!/usr/bin/env python3
"""Exact rational-function extraction for the sole extra S-unit guard."""
from pathlib import Path
from fractions import Fraction as Q
from math import lcm,gcd,prod
from sympy import QQ
from sympy.polys.fields import field
from collections import Counter
from itertools import product
import argparse,json
K,t=field('T',QQ)
Z,O=K.zero,K.one
def fold(x,r):
    a=[Z]*(len(x)+1)
    for j,v in enumerate(x):
        a[j]-=v*r;a[j+1]+=v
    return a
def conv(f,g):
    a=[Z]*(len(f)+len(g)-1)
    for j,v in enumerate(f):
       for k,w in enumerate(g):a[j+k]+=v*w
    return a
def hull(S):
    m=[O]
    for x in S:m=fold(m,x)
    return m
def moments(p,s=0,d=1):
    return sum(v/(d*(j+s)+1)for j,v in enumerate(p))
def funcs(case,anchor):
    v=t*(12*t*t-45*t+40)/(15*(t-2)**2)
    a,b=v/t,2/t
    r,s=(b,a)if anchor=='b'else(a,b)
    if case==0:
      xi=O/2;E=r/2;D=1-E
      V=(2*E-1)**2
    elif case==1:
      xi=1/(2*r);E=O/2;D=1-xi
      V=(2*xi-1)**2
    else:
      xi=1/(1+r);E=1-xi;D=O/2
      V=(2*xi-1)**2
    h=xi*s
    H=hull((Z,xi,E,h))
    I=2*V/15-2*O/35
    J=2*V/35-2*O/63
    m=(O/9-J/I)/8
    # Q(1-X) = -1/4 (X-1)^2 (X-1/3)^2 - m (X-1)^2.
    U=hull([O,O]);J0=conv(U,hull([O/3,O/3]))
    pol=[-u/4-(m*U[j]if j<3 else 0)for j,u in enumerate(J0)]
    G=conv(H,pol)
    R=moments(G,1)/moments(G)
    W=(2*R-1)**2; nodes=(Z,O,O/9,W,V)
    out={'xi':xi,'E':E,'D':D,'R':R,'old x':xi/t,'old v':xi*v/t}
    for n,x in enumerate(nodes):
        others=[z for z in nodes if z!=x]
        assert len(others)==4
        out['mass'+str(n)]=moments(hull(others),d=2)/prod(x-y for y in others)
    # These are literal entries of the protected low block, without a solve.
    sc=xi/t
    Lo=[
     [v*(4*v*v-13*v+12)/12,-3*v*v*(v-2)/4,v*v*(v-1)/3,-v*v*(v-3)*(v-1)/12,v*v*(v-2)*(v-1)/12],
     [(4*v**3-27*v*v+38*v-12)/12,-3*v*(v*v-6*v+4)/4,v*(v*v-6*v+2)/3,
      -v*(v-1)*(v*v-6*v+6)/12,v*(v-4)*(v-1)**2/12],
    ]
    for i,row in enumerate(Lo,6):
      for j,u in enumerate(row,1):out[f'A{i},{j}']=sc*u
    return out
def pad(c,n):return c+[0]*(n-len(c))
def integralfun(f):
    m=max(f.numer.degree(),f.denom.degree())
    ss=[[Q(int(x.get((i,),0).numerator),int(x.get((i,),0).denominator))for i in range(m+1)]for x in (f.numer,f.denom)]
    d=lcm(*(x.denominator for r in ss for x in r))
    n=tuple(tuple(int(a*d)for a in r)for r in ss)
    g=gcd(*(a for r in n for a in r))
    return tuple(tuple(a//g for a in r)for r in n)

def main():
    f=funcs(1,'b')['mass2']
    N,D=integralfun(f)
    assert N[0]==-2**21*3**7*5**2
    assert D[0]==0 and D[1]!=0
    print("case 1b early aggregate mass: exact numerator constant",N[0])
    print("integer denominator constant",D[0],"linear coefficient",D[1])
    print("at every unpaid prime, a positive valuation of theta forces a pole")
if __name__=='__main__':
    main()
