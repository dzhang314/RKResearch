#!/usr/bin/env python3
"""Exact rational 7th-row strong-order-five opening, plus literal all-tree checks."""
from fractions import Fraction as F
from functools import lru_cache
from math import prod,lcm
import json,sys
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def pmul(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c
def primitive(f):return sum(x/(i+1)for i,x in enumerate(f))
def cardinal(nodes,j):
    t=nodes[j];p=[F(1)]
    for k,x in enumerate(nodes):
        if k!=j:p=pmul(p,[-x/(t-x),1/(t-x)])
    return p
def table(p,q=None,e=F(1,10)):
    if q is None:q=(5*p-3)/(10*p-5)
    assert 10*p*q-5*p-5*q+3==0
    c=2*p/3;r=F(1)
    Z=F(0)
    nodes=[Z,p,q,r]
    assert len(set(nodes))==4 and e and c and c!=p
    w=list(map(primitive,[cardinal(nodes,i)for i in range(4)]))
    assert dot(w,[u**4 for u in nodes])==F(1,5)
    lp=3*p/4
    L=lambda x:3*x*x*(3*p-2*x)/(4*p*p)
    Ep=q*(q-p)/(c*(p-c))
    f=-(w[1]*lp+w[2]*L(q)+w[3]*L(r))/(w[3]*Ep)
    lr=L(r)+f*Ep
    kr=(r*r/2-lr*c-f*q)/p
    kq=(q*q/2-L(q)*c)/p
    Ar=[
        [],
        [e],
        [c-c*c/(2*e),c*c/(2*e)],
        [p-lp,Z,lp],
        [q-L(q)-kq,Z,L(q),kq],
        [r-lr-kr-f,Z,lr,kr,f],
        [w[0],Z,Z,w[1],w[2],w[3]],
    ]
    return [z+[Z]*(7-len(z))for z in Ar]
@lru_cache(None)
def trees(n):
    if n==1:return ((),)
    pool=[(j,s)for j in range(1,n)for s in trees(j)]
    def f(k,i):
        if k==0:yield ()
        for v in range(i,len(pool)):
            j,s=pool[v]
            if j>k:break
            for u in f(k-j,v):yield (s,)+u
    return tuple(f(n-1,0))
@lru_cache(None)
def size(t):return 1+sum(size(s)for s in t)
@lru_cache(None)
def fact(t):return size(t)*prod(fact(s)for s in t)
def verify(A):
    @lru_cache(None)
    def phi(t):
        if not t:return [F(1)]*len(A)
        return [prod(z)for z in zip(*(primitive(s)for s in t))]
    @lru_cache(None)
    def primitive(t):return [dot(a,phi(t))for a in A]
    n=0
    for k in range(1,7):
        for t in trees(k):
            assert phi(t)[6]==F(k,fact(t));n+=1
    assert n==37
    print('Exact 37 local derivative profiles through size six.')
    bad=[t for t in trees(7)if phi(t)[6]!=F(7,fact(t))]
    assert bad
    print(len(bad),'size-seven derivative failures; first',bad[0],phi(bad[0])[6]-F(7,fact(bad[0])))
    tail=lambda u:() if not u else (tail(u-1),)
    assert dot(A[6],phi(tail(5)))!=F(1,fact(tail(5)))
    print('6th tall output',dot(A[6],phi(tail(5))))
if __name__=='__main__':
    A=table(F(3,10));verify(A)
    d=lcm(*(a.denominator for r in A[:6] for a in r[:6]))
    e=lcm(*(a.denominator for a in A[6][:6]))
    print('denominators',d,e)
    for row in A:print(*map(str,row))
    print('integer matrix',[[int(a*d)for a in row[:6]]for row in A[:6]])
    print('integer b',[int(a*e)for a in A[6][:6]])
    if len(sys.argv)>1:
        with open(sys.argv[1],'w')as f:json.dump(dict(A=[list(map(str,row))for row in A]),f,indent=2)
