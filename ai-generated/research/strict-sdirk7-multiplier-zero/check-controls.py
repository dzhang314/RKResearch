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
    for file in ['f19-arithmetic-second', 'f19-arithmetic-fourth']:
        d=json.loads(Path(__file__).with_name(file+'.json').read_text())
        A,b,z=d['tableau'],d['b'],d['z']
        assert verify(A,b,19,freeze(d['eighth_tree']))==d['eighth_residue']
        assert d['eighth_residue']
        assert all(row[i]*z%19==1 and not any(row[i+1:]) for i,row in enumerate(A))
        assert b[:2]==[0,0] and all(b[2:])
        B=[[z*a%19 for a in row] for row in A]
        x=[sum(row)%19 for row in B]
        y=[(z-a)%19 for a in x]
        assert y[2:]==d['y'] and len(set(y[2:]))==7
        act=list(range(2,9))
        DP=[(div(b[i]*y[i]**2,2)-sum(B[j][i]*b[j]*y[j] for j in range(9)))%19 for i in act]
        assert DP==d['D']
        px=[prod(y[i]-y[j] for j in act if i!=j)%19 for i in act]
        poly=lambda p,y:sum(a*y**i for i,a in enumerate(p))%19
        w=[poly(d['W'],y[i]) for i in act]
        assert all(w) and all((j*k-d['tau']*v)%19==0 for j,k,v in zip(DP,px,w))
        Bx=[sum(a*z for a,z in zip(row,x))%19 for row in B]
        C=[(sum(a*z for a,z in zip(B[i],Bx))-div(x[i]**3,6))%19 for i in act]
        VV=d['V']; sc=div(C[0],VV[0])
        assert sc and all((a-sc*b)%19==0 for a,b in zip(C,VV))
        if 'e' in d:
            e=d['e']
            assert [y[i] for i,v in zip(act,VV) if not v]==[e]
            n=lambda y:div(2*y,z)-1
            L=lambda y:[1,y,div(3*y*y-1,2),div(5*y**3-3*y,2)]
            g=lambda y:sum((2*k+1)*p*q for k,(p,q) in enumerate(zip(L(n(e)),L(n(y)))))%19
            i=y.index(e,2)
            assert b[i]*g(e)%19==d['gram_id']!=1
            assert all((d['tau']*W*V-(y[i]-e)*g(y[i]))%19==0 for i,W,V in zip(act,w,VV))
        else:
            assert all(VV)
            assert all((W*V-poly(d['g'],y[i]))%19==0 for i,W,V in zip(act,w,VV))
        print(file, "85 rooted orders, next-order failure, and actual adjoint/defect profiles verified")
