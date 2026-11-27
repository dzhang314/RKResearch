#!/usr/bin/env python3
"""Independent exact midpoint replay of the emitted 14-row interval fixture."""
from functools import cache
from fractions import Fraction as Q
from math import prod
import itertools, json, sys

def main(path):
    obj=json.load(open(path))
    den=2**(obj['bits']+1)
    mid=lambda t:Q(sum(t),den)
    A=[[mid(t)for t in row]for row in obj['A']]; b=list(map(mid,obj['b']))
    assert len(A)==len(b)==14 and all(len(r)==14 for r in A)
    assert all(A[i][j]==0 for i in range(14) for j in range(i+1,14))
    assert len({A[i][i] for i in range(14)})==1 and A[0][0]>0
    kind={1:{'()':()}}
    @cache
    def options(n,i):
        if n==0:return ((),)
        dst=[]
        for j in range(i,len(pool)):
            s,r=pool[j]
            if s>n:break
            dst.extend((r,)+w for w in options(n-s,j))
        return tuple(dst)
    for n in range(2,10):
        pool=sorted((k,t)for k,d in kind.items()for t in d)
        options.cache_clear()
        kind[n]={'('+''.join(t)+')':t for t in options(n-1,0)}
    known=dict(itertools.chain.from_iterable(d.items()for d in kind.values()))
    def size(key): return len(key)//2
    @cache
    def tf(t):return size(t)*prod(tf(c)for c in known[t])
    @cache
    def phi(t):
        if t=='()': return (Q(1),)*14
        return tuple(prod(prim(c)[i]for c in known[t]) for i in range(14))
    @cache
    def prim(t):return tuple(sum(v*w for v,w in zip(row,phi(t))) for row in A)
    cts=[len(kind[k])for k in range(1,10)]
    assert cts==[1,1,2,4,9,20,48,115,286]
    worst=max(abs(sum(u*v for u,v in zip(b,phi(t)))-1/Q(tf(t))) for t in known)
    assert worst<Q(1,2**125)
    bush='('+'()'*9+')'
    assert abs(sum(u*v for u,v in zip(b,phi10_bush(A)))-Q(1,10))>Q(1,2**18)
    print('independent exact midpoint: 486 rooted deviations < 2^-125; next bush deviation > 2^-18')
def phi10_bush(A):return [sum(row)**9 for row in A]
if __name__=='__main__':main(sys.argv[1])
