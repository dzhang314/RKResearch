#!/usr/bin/env python3
"""Exact cross-diagonal gates via the neighboring authenticated Lobatto data."""
from pathlib import Path
import sys
from hashlib import md5
from math import prod
src=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).parent.parent/'erk10-stepanov-five-opening'/'stepanov15-source.txt'
B=src.read_bytes()
assert md5(B).hexdigest()=='be9e5e3ba1ff8ed21124ad285d7d2fd5'
p=227;x,y,z=177,190,149
assert (x*x-3)%p==0 and (y*y-7)%p==0 and (z*z-147-42*y)%p==0
def decode(row):
    a,b,c,d,e,f,g,h,q=map(int,row.split())
    return (63*a+63*b*x+63*c*y+63*d*x*y+3*e*z+
        (-2*f+7*h)*x*z+3*g*y*z+(f-2*h)*x*y*z)*pow(63*q,-1,p)%p
D=list(map(decode,B.splitlines()))
c,b=D[:15],D[15:30]
s=[c[i]for i in (8,10,6,7)]
w=[(b[i]+b[j])%p for i,j in [(8,9),(10,11),(6,12),(7,13)]]+[b[-1]]
y=s+[1]
G=[w[i]*prod(a-b for b in y if b!=a)%p for i,a in enumerate(y)]
assert s==[51,24,204,177] and G==[128,137,64,67,158]
def mul(F,a):
    g=[0]*(len(F)+1)
    for i,v in enumerate(F):g[i]=(g[i]-a*v)%p;g[i+1]=(g[i+1]+v)%p
    return g
def I(F,r):return sum(x*r**(i+1)*pow(i+1,-1,p)for i,x in enumerate(F))%p
for j,a in enumerate(s):
    F=[0,1]
    for i,t in enumerate(s):
        if i!=j:F=mul(F,t)
    for i,b in enumerate(s):
        if i!=j:
            coeff=(G[i]*I(F,b)-G[j]*I(F,a))%p
            assert coeff
            print('unused column',j,'other row',i,'uncancelled residue',coeff)
print('All 12 ordered cross-diagonal primitive gates nonzero mod 227.')
