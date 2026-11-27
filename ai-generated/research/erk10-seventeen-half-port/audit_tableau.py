#!/usr/bin/env python3
"""Integer-only rooted replay on literal coefficients, without the construction."""
from argparse import ArgumentParser
from fractions import Fraction as F
from functools import lru_cache
from math import prod, lcm, gcd, factorial
from pathlib import Path
import json

def audit(path, single=False):
    data=json.loads(path.read_text())
    n=len(data['A'])
    assert len(data['b'])==n and n == 17
    assert [len(r)for r in data['A']]==list(range(n))
    A=[list(map(F,row))for row in data['A']];b=list(map(F,data['b']))
    D=lcm(*(x.denominator for x in (*b,*(x for r in A for x in r))))
    assert factorial(10)**3%D==0
    assert D==int(data['D'])
    M=[tuple(int(x*D)for x in r)for r in A]
    print('Literal physical rows',n,'common denominator',D)
    assert len({row+(0,)*(n-len(row))for row in M})==n
    w=tuple(int(x*D)for x in b)
    def act(v):return tuple(sum(x*y for x,y in zip(row,v))for row in M)
    def out(v):return sum(x*y for x,y in zip(w,v))
    V=[(1,)*n]; W=[act(V[0])]
    Tree=[()]; Orders=[1]; Gammas=[1]
    counts=[1]
    assert out(V[0])==D
    for q in range(2,12 if single else 11):
        lim=len(Tree)
        @lru_cache(None)
        def forests(rem,least=0):
            if not rem:return ((),)
            return tuple((i,*r)for i in range(least,lim) if Orders[i]<=rem
                         for r in forests(rem-Orders[i],i))
        group=forests(q-1)
        if q<=10:counts.append(len(group))
        for kids in group:
            v=tuple(prod(W[j][i]for j in kids)for i in range(n))
            gamma=q*prod(Gammas[j]for j in kids)
            z=out(v)*gamma
            if q<=10:
                assert z==D**q,(q,kids,z)
            elif z!=D**11:
                r=F(z,D**11)-1
                if factorial(10)**40%abs(r.numerator)==0:
                    t=tuple(Tree[i]for i in kids)
                    print('First singleton unit defect',r,'tree',t,flush=True)
                    single=False
                    break
            Tree.append(tuple(Tree[i]for i in kids)); Orders.append(q); Gammas.append(gamma)
            V.append(v); W.append(act(v))
    assert counts==[1,1,2,4,9,20,48,115,286,719] and sum(counts)==1205
    def make(t):return tuple(map(make,t))
    @lru_cache(None)
    def phi(t):
        vals=tuple(map(ext,t))
        return tuple(prod(x[i]for x in vals)for i in range(n))
    @lru_cache(None)
    def ext(t):return act(phi(t))
    def nvert(t):return 1+sum(map(nvert,t))
    def fac(t):return nvert(t)*prod(map(fac,t))
    g=0
    # Independently evaluate the exactness receipts from their serialized trees.
    for tree,value in data['defects']:
        t=make(tree)
        assert nvert(t)==11
        r=F(fac(t)*out(phi(t)),D**11)-1
        assert r==F(value)
        assert factorial(10)**40%r.denominator==0
        g=gcd(g,r.numerator)
        print('Eleventh defect',r,'tree',t)
    assert g and factorial(10)**40%g==0
    assert n==17 and D==2**7*3**6*5**2*7**3
    bush9=((),)*8
    t=((),bush9)
    assert nvert(t)==11 and fac(t)==99
    raw=F(out(phi(t)),D**11)
    assert raw==F(7069,699840)
    unit=fac(t)*raw-1
    assert unit==F(-1,77760) and factorial(10)**3%unit.denominator==0
    print('Selected single unit defect',unit,', factorial',fac(t),', raw output',raw)
    print('All paid conditions',counts,'total',sum(counts),'; order-eleven numerator gcd',g)

if __name__=='__main__':
    p=ArgumentParser(description=__doc__)
    p.add_argument('source',type=Path,nargs='?',default=Path(__file__).with_name('tableau.json'))
    p.add_argument('--single',action='store_true')
    a=p.parse_args();audit(a.source,a.single)
