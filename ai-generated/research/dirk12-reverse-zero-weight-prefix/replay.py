#!/usr/bin/env python3
"""Independent literal exact quadrature and modulus-37 obstruction."""
from fractions import Fraction as Q
from math import prod, gcd, factorial
def pprod(xs):
    p=[Q(1)]
    for t in xs:p=[-t*p[0]]+[a-t*b for a,b in zip(p,p[1:])]+[p[-1]]
    return p
def weight(xs,x):
    u=[t for t in xs if t!=x]
    return sum(a/(i+1) for i,a in enumerate(pprod(u)))/prod(x-t for t in u)
g=tuple(Q(j,8) for j in range(13) if j!=9)
r=[x for x in g if x not in (0,1)]
W={x:weight(g,x) for x in g}
assert all(sum(w*x**k for x,w in W.items())==Q(1,k+1) for k in range(12))
p,q,z=Q(5,4),Q(3,2),Q(11,8)
C={x:Q(1)/(x*prod(x-t for t in r if t!=x)) for x in r}
h=1-p
assert 1-q==2*h
want=lambda x:W[x]*(1-x)*h*h/(6*C[x])
m=(want(q)-want(p))/(q-p)
G={x:C[x]*(want(p)+(x-p)*m) for x in r}
assert G[z]==C[z]*want(z)
assert all(sum(v*x**k for x,v in G.items())==0 for k in range(1,9))
def paid(d):
    while (z:=gcd(d,factorial(12)))>1:d//=z
    return d==1
assert all(paid(x.denominator) for x in (*W.values(),*G.values()))
F=37
mod=lambda x:x.numerator*pow(x.denominator,-1,F)%F
assert len(set(map(mod,g)))==12
assert W[p]==Q(148,31185) and W[q]==Q(962,5145525)
assert mod(W[p])==mod(W[q])==0
other=[(mod(1-x),mod(W[x])) for x in r if x not in (p,q,z)]
assert all(n and w for n,w in other)
assert all(not any((2*t*w*n-w*n*n)%F==0 and (3*t*w*n*n-w*n**3)%F==0
           for t in range(F)) for n,w in other)
print("degree-eleven scalar quadrature and paid affine cubic match: exact")
print("literal p=37 first two proper weight residues:",mod(W[p]),mod(W[q]))
print("remaining reflected-clock / weight residues:",other)
print("no low reverse continuation")
