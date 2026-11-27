#!/usr/bin/env python3
"""Independent integer replay of the literal 22-stage matrix, no constructor."""
from argparse import ArgumentParser
from fractions import Fraction as F
from functools import lru_cache
from math import factorial, lcm, gcd, prod
from pathlib import Path
from collections import Counter
import json

def audit(path, more=False):
    data=json.loads(path.read_text())
    n=len(data['A'])
    assert n==len(data['b'])==22 and [len(r)for r in data['A']]==list(range(n))
    A=[list(map(F,row))for row in data['A']];b=list(map(F,data['b']))
    D=lcm(*(x.denominator for x in (*b,*(x for r in A for x in r))))
    factors={};k=D
    for p in (2,3,5,7,11):
        r=0
        while k%p==0:r+=1;k//=p
        factors[p]=r
    assert k==1 and D==int(data['D'])==941072888448000
    assert factorial(11)**3%D==0
    M=[tuple(int(x*D)for x in r)for r in A]
    w=tuple(int(x*D)for x in b)
    assert len({r+(0,)*(n-len(r))for r in M})==n
    def act(v):return tuple(sum(x*y for x,y in zip(row,v))for row in M)
    def out(v):return sum(x*y for x,y in zip(w,v))
    V=[(1,)*n]; W=[act(V[0])]
    T=[()]; O=[1]; G=[1]
    counts=[1];un=[]
    assert out(V[0])==D
    for q in range(2,13 if more else 12):
        limit=len(T)
        @lru_cache(None)
        def forest(rem,least=0):
            if not rem:return ((),)
            return tuple((i,*r)for i in range(least,limit) if O[i]<=rem
                         for r in forest(rem-O[i],i))
        group=forest(q-1)
        if q<=11:counts.append(len(group))
        for ch in group:
            v=tuple(prod(W[j][i]for j in ch)for i in range(n))
            gamma=q*prod(G[j]for j in ch)
            z=out(v)*gamma
            t=tuple(T[i]for i in ch)
            if q<=11:
                assert z==D**q,(q,ch,z)
                T.append(t);O.append(q);G.append(gamma);V.append(v);W.append(act(v))
            elif z!=D**12:
                f=F(z,D**12)-1
                if factorial(11)**40%abs(f.numerator)==0:
                    un.append((gamma,t,f))
    assert counts==[1,1,2,4,9,20,48,115,286,719,1842] and sum(counts)==3047
    def mak(t):return tuple(map(mak,t))
    @lru_cache(None)
    def phi(t):
        js=tuple(map(ext,t))
        return tuple(prod(r[i]for r in js)for i in range(n))
    @lru_cache(None)
    def ext(t):return act(phi(t))
    def order(t):return 1+sum(map(order,t))
    def fact(t):return order(t)*prod(map(fact,t))
    g=0
    for tree,defect in data['defects']:
        t=mak(tree)
        assert order(t)==12
        v=F(fact(t)*out(phi(t)),D**12)-1
        assert v==F(defect)
        assert factorial(11)**40%v.denominator==0
        g=gcd(g,v.numerator)
        print('Twelfth defect',v,'factorial',fact(t),'tree',t)
    assert g==1
    b5=((),)*4
    t=((),(),(),(((b5,),),))
    assert order(t)==12 and fact(t)==20160
    raw=F(out(phi(t)),D**12)
    assert raw==F(2657,53887680) and fact(t)*raw-1==F(-16,2673)
    assert factorial(11)**6%2673==0 and factorial(11)**6%16==0
    print('Selected single unit defect -16/2673, factorial 20160, raw output',raw)
    print('Strict distinct rows',n,'common denominator',D,factors)
    print('All exact paid conditions',counts,'total',sum(counts),'next numerator gcd',g)
    if un:
        print('Singleton units',len(un))
        for gamma,t,r in sorted(un)[:16]:print(gamma,t,r)

if __name__=='__main__':
    p=ArgumentParser(description=__doc__)
    p.add_argument('source',type=Path,nargs='?',default=Path(__file__).with_name('tableau.json'))
    p.add_argument('--more',action='store_true')
    a=p.parse_args();audit(a.source,a.more)
