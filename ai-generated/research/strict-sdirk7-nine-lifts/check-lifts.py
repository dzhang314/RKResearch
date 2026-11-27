#!/usr/bin/env python3
"""Check the literal lift ledger without Jacobians or the construction."""
from functools import cache
from itertools import product, combinations_with_replacement
from math import prod, gcd
from pathlib import Path
import json

# Partition the child-size multiset first, then choose children of each size.
# A leaf has empty tuple; children are canonically sorted recursively.
def partitions(n, lo=1):
    if not n:
        yield ()
    for i in range(lo, n+1):
        for tail in partitions(n-i, i):
            yield (i,)+tail

def catalog(n):
    by_size={1:[()]}
    for m in range(2,n+1):
        layer=set()
        for children in partitions(m-1):
            counts={n:children.count(n) for n in set(children)}
            options=[combinations_with_replacement(by_size[n],k) for n,k in counts.items()]
            for forest in product(*options):
                layer.add(tuple(sorted(t for group in forest for t in group)))
        by_size[m]=sorted(layer)
    return by_size

@cache
def size(t):
    return 1+sum(size(s) for s in t)

@cache
def factorial(t):
    return size(t)*prod(factorial(s) for s in t)

def verify(table,N,counts):
    m,A,b = table['modulus'],table['A'],table['b']
    assert m==N and len(A)==len(b)==9
    g=A[0][0]
    assert gcd(g,N)==1
    assert all(len(row)==9 and row[i]==g and all(a==0 for a in row[i+1:]) for i,row in enumerate(A))

    @cache
    def stage(t,i):
        return prod(sum(A[i][j]*stage(s,j) for j in range(i+1)) for s in t)%N

    def condition(t):
        return (factorial(t)*sum(bi*stage(t,i) for i,bi in enumerate(b)))%N

    assert all(condition(t)==1 for col in counts.values() for t in col)
    fail=condition(((),)*7)
    assert fail==table['next-bush-value'] and gcd(fail-1,N)==1

def reduce(rec,m):
    return {'modulus':m,'A':[[a%m for a in row] for row in rec['A']],
            'b':[b%m for b in rec['b']],'next-bush-value':rec['next-bush-value']%m}

if __name__=='__main__':
    d=json.loads(Path(__file__).with_name('nine-stage-19-power-lifts.json').read_text())
    cat=catalog(7)
    assert [len(cat[j]) for j in range(1,8)]==[1,1,2,4,9,20,48]
    p=d['p']; kmax=d['highest-k']; top=d['top']
    assert (p,kmax)==(19,12)
    assert reduce(top,p)==d['residue'] and reduce(top,p**2)==d['square']
    for k in range(1,kmax+1):
        verify(reduce(top,p**k),p**k,cat)
    print('Independently checked all 85 rooted conditions and unit next-bush failure modulo each 19^k, 1 <= k <= 12.')
