#!/usr/bin/env python3
"""Independent standard-library exact replay of the literal rational tableau."""
from fractions import Fraction as F
from math import lcm, prod
from pathlib import Path
from functools import lru_cache
import json
import sys

def factorial(t):
    return size(t)*prod(factorial(u) for u in t)
@lru_cache(None)
def size(t):return 1+sum(size(u) for u in t)

# Build multisets of children from previously generated grades, ordered
# by the grade catalog. No stage/moment data enter the enumeration.
def catalog(cap):
    by_n={1:[()]}
    for n in range(2,cap+1):
        opts=[u for k in range(1,n) for u in by_n[k]]
        def f(m,j):
            if m==0:
                yield ()
                return
            for i in range(j,len(opts)):
                u=opts[i]
                if size(u)>m:break
                for tail in f(m-size(u),i):
                    yield (u,)+tail
        by_n[n]=list(f(n-1,0))
    return by_n

def check(path):
    fixture=json.loads(path.read_text())
    N=len(fixture["A"])
    assert N==14 and [len(r) for r in fixture["A"]]==list(range(N))
    Q=[list(map(F,r)) for r in fixture["A"]]
    bq=list(map(F,fixture["b"]))
    D=lcm(*(x.denominator for row in Q for x in row),*(x.denominator for x in bq))
    assert D==3941167085856000
    A=[tuple(int(D*x) for x in row)+(0,)*(N-i) for i,row in enumerate(Q)]
    assert len(set(A))==14
    b=tuple(int(D*v) for v in bq)
    c=tuple(sum(r) for r in A)
    phi={(): (1,)*N}
    children={():c}
    dot=lambda a,v:sum(x*y for x,y in zip(a,v) if x and y)

    def value(t):
        if t not in phi:
            phi[t]=tuple(prod(action(ch)[j] for ch in t) for j in range(N))
        return phi[t]
    def action(t):
        if t not in children:
            z=value(t)
            children[t]=tuple(dot(row,z) for row in A)
        return children[t]

    by_n=catalog(9)
    count=[len(by_n[k]) for k in range(1,10)]
    assert count==[1,1,2,4,9,20,48,115,286]
    for n,ts in by_n.items():
        assert all(factorial(tree)*dot(b,value(tree))==D**n for tree in ts)
    assert all((k+1)*dot(b,[x**k for x in c])==D**(k+1) for k in range(9))
    fifth=F(10*dot(b,[x**9 for x in c]),D**10)-1
    assert fifth==-F(1,2160)
    tall=()
    for i in range(9):tall=(tall,)
    tt=F(factorial(tall)*dot(b,value(tall)),D**10)-1
    assert tt==-F(7167,32500)
    assert all(F(sum(A[k][j]*b[k] for k in range(N)),D**2)==F(b[j]*(D-c[j]),D**2) for j in range(6,N))
    # The D(1) equality claimed is on the later columns; no full
    # order-ten equality is inferred for the old donor columns.
    print("Strict, fourteen pairwise distinct rows; shared denominator",D)
    print("All 486 ordinary order conditions through nine:",count)
    print("Order-ten bush and tall normalized defects:",fifth,tt)
    print("Scalar precision exactly eight; no floating-point inputs used.")
if __name__=="__main__":
    check(Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name("tableau.json"))
