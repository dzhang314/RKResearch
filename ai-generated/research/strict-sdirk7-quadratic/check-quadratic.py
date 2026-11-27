#!/usr/bin/env python3
"""Independent exact rooted check; no use of the construction equations."""
from functools import cache
from itertools import combinations_with_replacement, product
from math import gcd, lcm, prod, isqrt
from pathlib import Path
import json
from quadratic import Quad as K, RADICAND

def partitions(n, lo=1):
    if not n:
        yield ()
    for j in range(lo,n+1):
        for p in partitions(n-j,j):
            yield (j,)+p

def trees(n):
    d={1:[()]}
    for j in range(2,n+1):
        t=set()
        for parts in partitions(j-1):
            combos=[combinations_with_replacement(d[k],parts.count(k)) for k in set(parts)]
            for s in product(*combos):
                t.add(tuple(sorted(v for f in s for v in f)))
        d[j]=sorted(t)
    assert [len(d[j]) for j in range(1,n+1)]==[1,1,2,4,9,20,48][:n]
    return [t for j in range(1,n+1) for t in d[j]]

@cache
def size(t):
    return 1+sum(size(c) for c in t)

@cache
def factorial(t):
    return size(t)*prod(factorial(c) for c in t)

def check(A,b,d,reduce,gamma):
    n=len(A)
    assert n==len(b)==9
    assert all(len(row)==n and row[i]==gamma and not any(row[i+1:]) for i,row in enumerate(A))
    @cache
    def stage(t,i):
        return reduce(prod(sum(A[i][j]*stage(s,j) for j in range(i+1)) for s in t))
    def value(t):
        return reduce(factorial(t)*sum(w*stage(t,i) for i,w in enumerate(b)))
    assert all(value(t)==1 for t in d)
    w=value(((),)*7)
    assert w!=1
    return w

if __name__=='__main__':
    data=json.loads(Path(__file__).with_name('nine-stage-quadratic.json').read_text())
    assert data['radicand']==RADICAND
    assert isqrt(RADICAND)**2<RADICAND
    A=[[K(*v) for v in row] for row in data['A']]
    b=[K(*v) for v in data['b']]
    ad=lcm(*(e.denominator for row in A for v in row for e in (v.a,v.b)))
    bd=lcm(*(e.denominator for v in b for e in (v.a,v.b)))
    cat=trees(7); assert len(cat)==85
    bush=check(A,b,cat,K,K(data['gamma']))
    assert bush==K(*data['eighth-bush'])
    ee=bush-1; den=lcm(ee.a.denominator,ee.b.denominator)
    defect=ee*den; nn=defect.norm()
    assert nn==-1545982860640624199651
    assert gcd(ad*bd*int(nn),19)==1
    print('All 85 exact quadratic conditions, including unit-residual exactness data, verified.')
    for start,receipt in ((4,6),(15,17)):
        v = check([[x.mod(start,19) for x in row] for row in A],
                  [x.mod(start,19) for x in b],cat,lambda x:x%19,pow(4,-1,19))
        assert v==receipt
    r,m=4,19
    for k in range(1,13):
        vv=check([[x.mod(r,m) for x in row] for row in A],
                 [x.mod(r,m) for x in b],cat,lambda x:x%m,pow(4,-1,m))
        assert vv%19==6
        assert (r*r-RADICAND)%m==0
        e=(r*r-RADICAND)//m
        r=(r-12*m*e)%(19*m); m*=19
    print('Direct modulo-19 failed bush values are 6 and 17; twelve simple-root specializations also replayed.')
