#!/usr/bin/env python3
"""Literal rational opening, true local trees, quotient and paid rank checks."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import permutations
from math import lcm,prod
from pathlib import Path
import argparse,json

A=[[],[F(1,8)],[-F(1,9),F(4,9)],[-F(5,64),F(3,8),-F(3,64)],
   [-F(1,14),F(3,7),F(3,7),-F(2,7)]]
c=tuple(map(sum,A))
assert c==(0,F(1,8),F(1,3),F(1,4),F(1,2))

def ap(v):return tuple(sum(a*b for a,b in zip(row,v)) for row in A)
def cp(k):return tuple(x**k for x in c)
def sub(u,v):return tuple(x-y for x,y in zip(u,v))
def scale(k,v):return tuple(k*x for x in v)
def det(row):
    n=len(row)
    return sum((-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))*
             prod(row[i][p[i]] for i in range(n)) for p in permutations(range(n)))
def rank(row):
    z=[list(map(F,r))for r in row];i=0
    for j in range(len(z[0])):
        k=next((k for k in range(i,len(z))if z[k][j]),None)
        if k is None:continue
        z[i],z[k]=z[k],z[i]
        for k in range(i+1,len(z)):
            a=z[k][j]/z[i][j]
            z[k]=[u-a*v for u,v in zip(z[k],z[i])]
        i+=1
    return i

def solve(M,b):
    n=len(M)
    d=det(M)
    assert d
    return [det([[v if j==k else x for j,x in enumerate(row)]for row,v in zip(M,b)])/d for k in range(n)]

def tree_groups(n):
    g={1:[()]}
    for m in range(2,n+1):
        T=[(t,s)for s in range(1,m)for t in g[s]]
        def forests(k,j=0):
            if not k:yield ()
            else:
                for i in range(j,len(T)):
                    t,s=T[i]
                    if s>k:break
                    for ts in forests(k-s,i):yield (t,)+ts
        g[m]=list(forests(m-1))
    return g

@lru_cache(None)
def size(t):return 1+sum(size(s)for s in t)

@lru_cache(None)
def phi(t):
    a=[scale(size(s),ap(phi(s)))for s in t]
    return tuple(prod(z[i]for z in a)for i in range(5))

G=tree_groups(5)
assert [len(G[i])for i in range(1,6)]==[1,1,2,4,9]
alpha,beta=F(27,32),F(27,28)
def lo(v):return v[0],v[3]-alpha*v[2],v[4]-beta*v[2]
M=list(map(list,zip(*(lo(cp(i))for i in range(3)))))
Pi=[solve(M,lo(tuple(F(int(i==j))for i in range(5))))for j in range(5)]
def decoder(v):return tuple(sum(w[i]*z for w,z in zip(Pi,v))for i in range(3))
assert det(M)==F(1,896)
print('literal quotient determinant',det(M),'decoder coordinate columns',Pi)
rem=[(1,0,0),(0,1,0),(0,0,1),(0,F(1,2),0)]
for j in range(1,5):
    for t in G[j]:assert decoder(phi(t))==tuple(map(F,rem[j-1]))
print('all 8 actual profiles through size four realize the model modulo P')

for n,expected in ((4,(5,2,6)),(5,(5,4,9))):
    alltrees=[t for j in range(1,n+1)for t in G[j]]
    pr=[phi(t)for t in alltrees]
    dv=[sub(phi(t),cp(size(t)-1))for t in alltrees]
    joint=[tuple(v)+tuple(int(i==size(t)-1)for i in range(n))
           for t,v in zip(alltrees,pr)]
    facts=rank(pr),rank(dv),rank(joint)
    assert facts==expected
    print('through size',n,'actual/pure/joint ranks',facts)

d=sub(ap(c),scale(F(1,2),cp(2)))
ad=ap(d)
cad=tuple(x*y for x,y in zip(c,ad))
aad=ap(ad)
pd=det(list(zip(d[1:],ad[1:],cad[1:],aad[1:])))
assert pd==-F(1,541165879296)
D=lcm(*(z.denominator for row in A for z in row))
Q=lcm(*(z.denominator for row in Pi for z in row))
print('paid row/decoder denominator',D,Q,'pure pivot determinant',pd)
assert D==4032 and all(F(3628800**5,n).denominator==1 for n in (D,Q,pd.denominator))
print('common-denominator integer minor',pd*(16*D**13))
def P(z):return z**3-z/2
def JP(z):return z**4/4-z*z/4
high=[F(1),F(2,3)]
B=[[],[JP(high[1])/P(high[0])]]
Aplus=A[:]
for i,(x,taps) in enumerate(zip(high,B)):
    drift=[x**(j+1)/(j+1)-sum(v*high[k]**j for k,v in enumerate(taps))
           for j in range(3)]
    old=[sum(a*b for a,b in zip(w,drift)) for w in Pi]
    Aplus.append(old+taps)
assert B[1]==[-F(10,81)] and all(sum(Aplus[5+i])==z for i,z in enumerate(high))
@lru_cache(None)
def phiplus(t):
    cs=[(size(s),phiplus(s))for s in t]
    return tuple(prod(m*sum(a*b for a,b in zip(row,v)) for m,v in cs) for row in Aplus)
assert all(phiplus(t)[5:]==tuple(z**(size(t)-1)for z in high)
           for j in range(1,6)for t in G[j])
bush6=((),)*5
t7=(bush6,)
# The normalized local size-six tall-child-of-bush5 defect, [bush5].
u=(((),)*4,)
assert phiplus(u)[5]==F(5,6)
print('first two true high rows',Aplus[5:])
print('true high profiles through size five: 34 paid checks, nonzero high tap',B[1][0])
print('first high row normalized size-six [bush5] value',phiplus(u)[5])
data={
    "description":"Literal five-row opening, not a full order-ten tableau",
    "A":[[str(z)for z in r]for r in A],
    "clocks":[str(z)for z in c],
    "kernel_P_ascending":["0","-1/2","0","1"],
    "decoder_columns_ascending":[[str(z)for z in r]for r in Pi],
    "pure_minor":str(pd),
    "first_two_high_A_rows":[[str(z)for z in row]for row in Aplus[5:]],
}
js=json.dumps(data,indent=2)+'\n'
a=argparse.ArgumentParser()
a.add_argument('--emit',type=Path)
args=a.parse_args()
if args.emit:args.emit.write_text(js)
else:assert js==Path(__file__).with_name('seed.json').read_text()
