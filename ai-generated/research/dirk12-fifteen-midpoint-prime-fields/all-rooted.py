#!/usr/bin/env python3
"""Independent direct prime-ring replay of the literal coefficients."""
from functools import cache
from math import isqrt,prod
from pathlib import Path
import json,sys
@cache
def trees(n):
    if n==1:return ((),)
    pool=[(i,t) for i in range(1,n) for t in trees(i)]
    def forests(rem,start):
        if not rem:
            yield ();return
        for j in range(start,len(pool)):
            w,t=pool[j]
            if w>rem:break
            for tail in forests(rem-w,j):yield (t,)+tail
    return tuple(forests(n-1,0))
@cache
def size(t):return 1+sum(map(size,t))
@cache
def density(t):return size(t)*prod(map(density,t))
def direct(data,prime,power=1):
    assert not any(prime%a==0 for a in range(2,isqrt(prime)+1))
    p=prime**power
    A,b,c=data['A'],data['b'],data['c']
    assert len(A)==len(b)==len(c)==15
    assert all(len(row)==15 and all(0<=v<p for v in row) and all(x==0 for x in row[i+1:])
               for i,row in enumerate(A))
    assert all(0<=v<p for v in b+c)
    assert tuple(i+1 for i,v in enumerate(b) if v==0)==(2,3,4,5)
    assert all(b[i]%prime for i in range(15) if i not in (1,2,3,4))
    assert A[0][0]==A[-1][-1]==0 and len({A[i][i]%prime for i in range(15)})>2
    assert [sum(row)%p for row in A]==c
    assert c[5]==pow(2,-1,p) and (2*c[6])%p==data['x'] and c[9]==data['f']
    assert c[11]==c[13]==(1-data['d'])%p
    @cache
    def stage(t):
        arr=[incoming(u) for u in t]
        return tuple(prod(q[i] for q in arr)%p for i in range(15))
    @cache
    def incoming(t):
        src=stage(t);return tuple(sum(a*u for a,u in zip(row,src))%p for row in A)
    def weighted(t):return sum(w*q for w,q in zip(b,stage(t)))%p
    count=[len(trees(n)) for n in range(1,13)]
    assert count==[1,1,2,4,9,20,48,115,286,719,1842,4766]
    for n in range(1,13):
        for t in trees(n):
            assert density(t)*weighted(t)%p==1,(p,t)
    h=(13*weighted(((),)*12)-1)%p
    assert h==data['defect'] and h%prime
    print(f"p={prime}, exponent={power}, x={data['x']}, f={data['f']}, d={data['d']}: {sum(count)} conditions, scaled order-13 bush {h}",flush=True)
if __name__=='__main__':
    paths=[Path(s) for s in sys.argv[1:]] or sorted(Path(__file__).parent.glob('witness-*.json'))
    assert paths
    for path in paths:
        dt=json.loads(path.read_text())
        direct(dt,dt['p'])
