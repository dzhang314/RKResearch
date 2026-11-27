#!/usr/bin/env python3
from math import prod
from functools import lru_cache
from pathlib import Path
import json

@lru_cache(None)
def size(t):return 1+sum(map(size,t))
@lru_cache(None)
def density(t):return size(t)*prod(map(density,t))
@lru_cache(None)
def trees(n):
    if n==1:return ((),)
    pool=tuple(t for k in range(1,n) for t in trees(k))
    def pick(start,left):
        if not left:yield ()
        for j in range(start,len(pool)):
            T=pool[j]
            d=left-size(T)
            if d<0:break
            for r in pick(j,d):yield (T,)+r
    return tuple(pick(0,n-1))


def verify(A,b,m,bad):
    @lru_cache(None)
    def stage(T):
        return tuple(prod(sum(v*w for v,w in zip(row,stage(U))) for U in T)%m for row in A)
    res=lambda T:(density(T)*sum(w*v for w,v in zip(b,stage(T)))-1)%m
    checks=[T for k in range(1,8) for T in trees(k)]
    assert len(set(checks))==85 and all(res(T)==0 for T in checks)
    return res(bad)


def div(a,b):return a*pow(b%19,-1,19)%19

if __name__=="__main__":
    freeze=lambda t:tuple(map(freeze,t))
    for tag in ('h2','q'):
        d=json.loads(Path(__file__).with_name(f'control-{tag}.json').read_text())
        A,b,z=d['tableau'],d['b'],d['z']
        assert verify(A,b,19,freeze(d['eighth_tree']))==d['eighth_residue']==6
        assert all(a[i]*z%19==1 and not any(a[i+1:]) for i,a in enumerate(A))
        assert b[:2]==[0,0] and all(b[2:])
        y=[z*(1-sum(row))%19 for row in A][2:]
        assert len(set(y))==7 and y==d['y']
        e=y[1];x=(z-e)%19;x_a=(z-y[0])%19;t=z*A[1][0]%19;M=x*x-4*x+2
        assert (e,x,x_a,t)==(d['e'],d['xe'],d['xa'],d['t'])
        nc=div(2*e,z)-1
        ps=[1,nc,div(3*nc*nc-1,2),div(5*nc**3-3*nc,2)]
        assert b[3]*sum((2*i+1)*a*a for i,a in enumerate(ps))%19==1
        if tag=='h2':
            assert x_a==(1+t)%19 and y[3]==z
            assert t==div(2*(x**3-6*x*x+9*x-3),3*M)
        else:
            assert (2-t)*x_a%19==(1-t)%19 and y[0]==0
            assert x_a==div(x*(x-2),2*(x-1))
            assert t==div(2*(x*x-3*x+1),M)
        print(tag,"all 85 rooted conditions, strict unit diagonal, exact next-order failure")
