#!/usr/bin/env python3
"""All possible preceding-clock support tests in the two-sweep co-order exclusion."""
from hashlib import md5
from itertools import combinations
from pathlib import Path
import sys
p=227
x,y,z=177,190,149
assert (x*x-3)%p==0 and (y*y-7)%p==0 and (z*z-147-42*y)%p==0
neigh=Path(__file__).parent.parent/'erk10-stepanov-five-opening'/'stepanov15-source.txt'
source=Path(sys.argv[1]) if len(sys.argv)>1 else neigh
buf=source.read_bytes()
assert md5(buf).hexdigest()=='be9e5e3ba1ff8ed21124ad285d7d2fd5'
def decode(r):
    a,b,c,d,e,f,g,h,q=r
    return (63*a+63*b*x+63*c*y+63*d*x*y+3*e*z+(-2*f+7*h)*x*z+
        3*g*y*z+(f-2*h)*x*y*z)*pow(63*q,-1,p)%p
c=[decode(list(map(int,row.split())))for row in buf.splitlines()[:15]]
nodes=[c[i]for i in (8,10,6,7)]
assert nodes==[51,24,204,177]
assert len(set(nodes+[0,1]))==6
def mul(F,a):
    g=[0]*(len(F)+1)
    for i,v in enumerate(F):g[i]=(g[i]-a*v)%p;g[i+1]=(g[i+1]+v)%p
    return g
test=[]
for r in nodes:
    for k in range(4):
        for S in combinations(nodes,k):
            F=[0,1]
            for a in S:F=mul(F,a)
            q=sum(v*pow(r,i+1,p)*pow(i+1,-1,p)for i,v in enumerate(F))%p
            assert q,(r,S)
            test.append((r,S,q))
assert len(test)==60
print('All 60 preceding-interior-clock hull primitive values nonzero mod 227.')
