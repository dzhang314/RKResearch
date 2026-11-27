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


if __name__=="__main__":
    d=json.loads(Path(__file__).with_name("f19-second.json").read_text())
    A,b=d["tableau"],d["b"]; p=19
    freeze=lambda t:tuple(map(freeze,t))
    assert verify(A,b,p,freeze(d["eighth_tree"]))==15
    assert all(a[i]==16 and not any(a[i+1:]) for i,a in enumerate(A))
    assert b[:2]==[0,0] and all(b[2:])
    y=[6*(1-sum(a))%p for a in A][2:]
    assert y==[5,16,13,0,17,9,1]
    e=y[1]
    def div(a,b):return a*pow(b%p,-1,p)%p
    leg=lambda t:[1,t,div(3*t*t-1,2),div(5*t**3-3*t,2)]
    norm=lambda t:div(t,3)-1
    g=lambda t:sum((2*j+1)*L*R for j,(L,R) in enumerate(zip(leg(norm(e)),leg(norm(t)))))%p
    assert (b[3]*g(e))%p==1 and g(e)==7
    u=y[-2];v=y[-3];M=(u*u-4*u+2)%p
    T=u**3-7*u*u+10*u-2;J=4*u**3-24*u*u+39*u-17
    r=[div(-1,2),div(M,2),div(M*J,2*T)]
    tree=[1,u,v]
    nu=[div(1,rj*prod(w-h for h in tree if h!=w)) for w,rj in zip(tree,r)]
    H=lambda t:sum(f*sum((2*j+1)*L*R for j,(L,R) in enumerate(zip(leg(norm(w)),leg(norm(t))))) for w,f in zip(tree,nu))%p
    assert H(e)==0
    c=y[3]
    assert [w for w in range(p) if (H(w)*g(c)-g(w)*H(c))%p==0]==[0,5,13]
    q2=div((u-3)*(u-2)**2,2*T);q1=div(-(u-3)*(u-1)*(2*u-3),T)
    f=lambda s:div(-4+(2*div(1,M)-2)*(s-1),3)
    E=lambda s:(-q1+q2*f(s)-div(1-s,M))%p
    l1=div(div(g(u),r[1])-div(g(1),r[0]),u-1)
    L=lambda s:(div(g(1),r[0])+l1*(s-1))%p
    a3=div(7*leg(norm(e))[3]*5,2*3**3)
    kap=(a3-q2*l1)%p; sig=div(-2*q2*(u-1)**3,3*M*T)
    assert kap and sig and L(c)
    assert [w for w in range(p) if (sig*L(w)+kap*E(w))%p==0]==[0]
    x=(6-e)%p;t=div(2*(div(x**3,3)-2*x*x+3*x-1),x*x-4*x+2)
    assert t==d['t']==9
    print("all 85 trees; eighth-bush residual 15; second-active Christoffel mass and linear chronology verified")
