#!/usr/bin/env python3
"""Exact all-parameter order and modular pruning obstruction."""
from argparse import ArgumentParser
from pathlib import Path
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from itertools import product
from math import prod,lcm
import json,sys

def factory(base):
    sys.path.insert(0,str(base))
    from build17 import prefix,construct,factory,trees,size,tf
    from scalar import dot,j0,lagrange,paid
    A0,Pi=prefix(base/'seed6-prefix.json')
    literal=json.loads((base/'tableau.json').read_text())
    assert sha256((base/'tableau.json').read_bytes()).hexdigest()=="663c5fbfb6b303a61d30ec39830628b715f88e3349979fe0813327405bc318c4"
    nodes=tuple(F(j,6)for j in range(-3,7))
    W={x:j0(lagrange(nodes,i))for i,x in enumerate(nodes)}
    c=tuple(map(F, literal['reverse_clocks']))
    w=list(map(F,literal['reverse_w']))
    U=list(map(F,literal['reverse_U']))
    E,*_=factory(c,w,U)
    p0=list(map(F,literal['free']))
    N=len(c); high=c[::-1]
    def mat(a,b):
        p=list(p0);p[0]+=a;p[1]+=b;p[4]+=b
        assert not any(E(p))
        K=E(p,True)[0]
        B=[[K[N-1-j][N-1-i]if i>j else F(0)for j in range(N)]for i in range(N)]
        P=[]
        for i,x in enumerate(high):
            C=[x**(d+1)/(d+1)-dot(B[i],[y**d for y in high])for d in range(5)]
            P.append([dot(C,[Pi[d][j]for d in range(5)])for j in range(9)])
        assert P[0]==A0[8]+[F(0)] and not any(B[0])
        A=[r+[F(0)]*(17-len(r))for r in A0]
        for h,r in zip(P[1:],B[1:]):
            h[8]+=r[0];A.append(h+r[1:])
        assert all(paid(x)for r in A for x in r)
        assert all(not any(r[i:])for i,r in enumerate(A))
        return [tuple(row[:i])for i,row in enumerate(A)]
    p=mat(F(0),F(0));A=mat(F(1),F(0));B=mat(F(0),F(1))
    U=[tuple(x-y for x,y in zip(r,s))for r,s in zip(A,p)]
    V=[tuple(x-y for x,y in zip(r,s))for r,s in zip(B,p)]
    assert [[str(x)for x in q]for q in p]==literal['A']
    assert all(sum(r)==0 for r in (*U,*V))
    assert mat(F(1),F(1))==[tuple(x+y+z for x,y,z in zip(r,s,t))for r,s,t in zip(p,U,V)]
    return (p,U,V,tuple(map(F,literal['b']))), (trees,size,tf)

def evaluator(A,n,p=0):
    @lru_cache(None)
    def phi(t):
        V=[act(u)for u in t]
        vals=tuple(prod(w[i]for w in V)for i in range(n))
        return tuple(x%p for x in vals) if p else vals
    @lru_cache(None)
    def act(t):
        v=phi(t)
        vals=tuple(sum(x*y for x,y in zip(r,v))for r in A)
        return tuple(x%p for x in vals) if p else vals
    return phi

def grid(P,U,V,w,trees,size,tf):
    n=len(P)
    den=lcm(*(x.denominator for M in (P,U,V)for r in M for x in r),*(x.denominator for x in w))
    assert 3628800**3%den==0
    ints=lambda M:[tuple(int(x*den)for x in r)for r in M]
    P,U,V=map(ints,(P,U,V))
    b=tuple(int(x*den)for x in w)
    ts=[(t,tf(t),den**size(t))for k in range(10)for t in trees(k)]
    assert len(ts)==1205
    count=0
    for a,c in product(range(10),repeat=2):
        A=[tuple(x+a*y+c*z for x,y,z in zip(r,s,t))for r,s,t in zip(P,U,V)]
        phi=evaluator(A,n)
        for t,g,d in ts:
            assert g*sum(x*y for x,y in zip(b,phi(t)))==d,(a,c,t)
            count+=1
    # Selected tree root children [leaf,bush9]. Row sums are fixed, so its
    # scalar output depends affinely on A. Three evaluations prove constant.
    g=99;t=((),((),)*8)
    for a,c in [(0,0),(1,0),(0,1)]:
        A=[tuple(x+a*y+c*z for x,y,z in zip(r,s,t))for r,s,t in zip(P,U,V)]
        phi=evaluator(A,n)
        assert F(g*sum(x*y for x,y in zip(b,phi(t))),den**11)-1==F(-1,77760)
    print('Exact integer tensor-grid receipts',count,'selected defect constant -1/77760')
    # One-tree obstruction to plain transfer to the old endpoint.
    t=(((),)*5,)
    for a,c in [(0,0),(1,0),(0,1)]:
        A=[tuple(x+a*y+c*z for x,y,z in zip(r,s,t))for r,s,t in zip(P,U,V)]
        vals=evaluator(A,n)(t)
        assert F(vals[7],den**6)==F(1,6)
        assert F(vals[-1]-vals[7],den**6)==F(-10,441)
    assert -42*w[-1]*F(-10,441)==F(2,45)
    print('Plain endpoint transfer creates cleared size-seven defect +2/45')

def modproof(P,U,V,w,trees,size,tf):
    p=11;n=len(P)
    mod=lambda q: q.numerator*pow(q.denominator,-1,p)%p
    mat=lambda M:[tuple(mod(q)for q in r)for r in M]
    P,U,V=map(mat,(P,U,V))
    assert mod(w[-1])==1
    stats=Counter()
    for a,c in product(range(p),repeat=2):
        A=[tuple((x+a*y+c*z)%p for x,y,z in zip(r,s,t))for r,s,t in zip(P,U,V)]
        phi=evaluator(A,n,p)
        B=[]
        done=False
        for k in range(9):
            if done:break
            for t in trees(k):
                v=list(phi(t))
                for j,row in B:
                    if v[j]:v=[(x-v[j]*y)%p for x,y in zip(v,row)]
                j=next((i for i,x in enumerate(v)if x),None)
                if j is None:continue
                inv=pow(v[j],-1,p)
                B.append((j,tuple(x*inv%p for x in v)))
                if len(B)==n:
                    stats[k+1]+=1;done=True;break
        assert done,(a,c,len(B))
    assert stats=={9:121}
    print('All 121 parameter pairs mod 11 have full profile rank 17 through order nine')

if __name__=='__main__':
    p=ArgumentParser(description=__doc__)
    p.add_argument('--base',type=Path,default=Path(__file__).parent.parent/'erk10-seventeen-half-port')
    s=p.parse_args()
    A,t=factory(s.base)
    modproof(*A,*t)
    grid(*A,*t)
