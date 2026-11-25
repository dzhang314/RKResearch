#!/usr/bin/env python3
"""Exact coefficient and arithmetic tests for the symmetric tall log-derivative identity."""
from fractions import Fraction as F
from itertools import product
from math import comb, factorial

def tr(a):
    a=list(a)
    while a and not a[-1]: a.pop()
    return a

def norm(a,q):return tr(a if q==0 else [u%q for u in a])
def term(a,i):return a[i] if i<len(a) else 0
def sub(a,b,q):return norm([term(a,i)-term(b,i) for i in range(max(len(a),len(b)))],q)
def mul(a,b,q):
    if not a or not b:return []
    v=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):v[i+j]+=x*y
    return norm(v,q)
def d(a,q):return norm([i*a[i] for i in range(1,len(a))],q)
def power(a,k,q):
    v=[1]
    for _ in range(k):v=mul(v,a,q)
    return v

def divrem(a,b,q):
    a=a[:]; assert b
    inv=pow(b[-1],-1,q) if q else F(1,b[-1]); v=[0]*(max(len(a)-len(b)+1,0))
    while len(a)>=len(b):
        j=len(a)-len(b);con=a[-1]*inv;v[j]=con
        for k,x in enumerate(b): a[j+k]-=con*x
        a=norm(a,q)
    return norm(v,q),a

def gcd(a,b,q):
    while b:a,b=b,divrem(a,b,q)[1]
    inv=pow(a[-1],-1,q) if q else F(1,a[-1]); return norm([x*inv for x in a],q)

def elem(A,q):return len(A)-len(gcd(A,d(A,q),q))

def check(P,Q,q,budget):
    assert P[0]==Q[0]==1 and (not q or budget<q)
    H=[pow(factorial(i)%q,-1,q) if q else F(1,factorial(i)) for i in range(budget+1)]
    E=sub(P,mul(Q,H,q),q); h=next((n-1 for n in range(budget+1) if term(E,n)),budget)
    GP,GQ=gcd(P,d(P,q),q),gcd(Q,d(Q,q),q)
    W=sub(sub(mul(Q,d(P,q),q),mul(P,d(Q,q),q),q),mul(P,Q,q),q)
    J,rem=divrem(W,mul(GP,GQ,q),q)
    assert not rem and W and len(W)-1==len(P)+len(Q)-2
    eP,eQ=len(P)-len(GP),len(Q)-len(GQ)
    assert J and len(J)-1==eP+eQ and h<=eP+eQ
    assert all(not term(J,j) for j in range(h))
    return h,eP,eQ

count=paid=0
for q,width in [(2,3),(3,3),(5,3),(7,2)]:
    polys=[tr([1,*v]) for v in product(range(q),repeat=width)]
    for P,Q in product(polys,repeat=2):
        h,_,_=check(P,Q,q,q-1);count+=1;paid+=h>0
print('Exhaustive normalized finite-field pairs checked, including noncoprime pairs:',count,'; positive contact:',paid)

pades=bothsaved=0
for a in range(1,6):
    for b in range(1,6):
        p=a+b
        for k in [1,2,3]:
            P0=[F(comb(a,i)*factorial(p-i),factorial(p)*k**i) for i in range(a+1)]
            Q0=[F((-1)**i*comb(b,i)*factorial(p-i),factorial(p)*k**i) for i in range(b+1)]
            P,Q=power(P0,k,0),power(Q0,k,0)
            h,eP,eQ=check(P,Q,0,p+1)
            assert (h,eP,eQ)==(p,a,b) and len(gcd(P,Q,0))==1
            if k>1:assert p<min(len(P)-1+eQ,len(Q)-1+eP);bothsaved+=1
            pades+=1
print('Rational simultaneous-multiplicity sharp Padé powers:',pades,'; strictly stronger than both unilateral bounds:',bothsaved)

for k in range(2,11):
    # Composition of k midpoint steps. Compute physical stages in the two order equations.
    g=F(1,2*k); c=[F(2*j+1,2*k) for j in range(k)]; B=[F(1,k)]*k
    assert sum(B)==1 and sum(v*w for v,w in zip(B,c))==F(1,2)
    P,Q=power([1,g],k,0),power([1,-g],k,0);h,eP,eQ=check(P,Q,0,3)
    assert (h,eP,eQ)==(2,1,1)
print('Literal order-two strict SDIRK branch, k=2,...,10: both raw degrees k, symmetric credits (1,1), actual p=2')

q=7;A=[1,1,4];B=[1]+[0]*6+[6]
assert check(A,B,q,6)==(2,2,0)
# Both numerator and denominator can have additional characteristic-divisible root multiplicities.
for u,v in [(2,3),(3,5),(4,2)]:
    P=mul(A,power([1,-u],q,q),q);Q=mul(B,power([1,-v],q,q),q)
    assert len(gcd(P,Q,q))==1 and check(P,Q,q,6)==(2,2,0)
print('F7 exact Frobenius credits verified, including added numerator and denominator labels; F7 actual p2 core e(P)=2,e(Q)=0')
