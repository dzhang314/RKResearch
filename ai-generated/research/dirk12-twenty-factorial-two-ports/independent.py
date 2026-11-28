"""Replay a literal tableau with a rooted tuple catalog and integer denominator clearing."""
from fractions import Fraction as Q
from functools import cache
from itertools import combinations_with_replacement, product
from math import factorial, gcd, lcm, prod
from pathlib import Path
import json
import sys

@cache
def partitions(n, low=1):
    if n == 0:
        return ((),)
    return tuple((k,) + p for k in range(low, n + 1) for p in partitions(n-k,k))

def main(path):
    o=json.loads(path.read_text())
    p,s=o['order'],o['stages']
    A=[[Q(y) for y in row] for row in o['A']]
    b=list(map(Q,o['b']))
    c=[sum(row) for row in A]
    assert (p,s)==(12,20)
    assert c==list(map(Q,o['c']))
    assert not any(A[i][j] for i in range(s) for j in range(i+1,s))
    assert A[0][0]==0 and A[1][1]==Q(1,16)
    da=lcm(*(y.denominator for row in A for y in row))
    db=lcm(*(y.denominator for y in b))
    D=lcm(da,db)
    assert D==o['common_denominator'] and factorial(p)**6%D==0 and D%16==0
    M=[[(j,int(x*da)) for j,x in enumerate(row) if x] for row in A]
    B=[int(x*db) for x in b]

    def act(v):
        return tuple(sum(x*v[j] for j,x in row) for row in M)
    def read(v):
        return sum(x*y for x,y in zip(B,v))
    trees=[[],[()]]
    for n in range(2,p+1):
        t=[]
        for ks in partitions(n-1):
            sizes=sorted(set(ks))
            blocks=[combinations_with_replacement(trees[k],ks.count(k)) for k in sizes]
            t.extend(tuple(a for g in groups for a in g) for groups in product(*blocks))
        trees.append(t)
    @cache
    def tree_data(t):
        ds=[tree_data(u) for u in t]
        n=1+sum(k for k,g,v in ds)
        gamma=n*prod(g for k,g,v in ds)
        v=tuple(prod(column) for column in zip(*(act(x) for k,g,x in ds))) if ds else (1,)*s
        return n,gamma,v
    counts=[len(t) for t in trees[1:]]
    assert counts==[1,1,2,4,9,20,48,115,286,719,1842,4766]
    for n,T in enumerate(trees[1:],1):
        assert len(T)==len(set(T))
        for t in T:
            k,g,v=tree_data(t)
            assert n==k and g*read(v)==db*da**(n-1),t
    v=(1,)*s
    for _ in range(p):
        v=act(v)
    den=db*da**p
    tall=Q(factorial(p+1)*read(v),den)-1
    bush=Q((p+1)*read(tuple(int(x*da)**p for x in c)),den)-1
    assert str(tall)==o['scaled_next_tall'] and str(bush)==o['scaled_next_bush']
    assert gcd(tall.numerator,bush.numerator)==1
    assert D**(p+1)%tall.denominator==D**(p+1)%bush.denominator==0
    print('Rooted tuples by order:',counts,'total:',sum(counts))
    print('Common denominator:',D,'divides (12!)^6; diagonal entries:',A[0][0],A[1][1])
    print('Scaled order-thirteen bush and tall numerators are coprime.')

if __name__=='__main__':
    main(Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('tableau20.json'))
