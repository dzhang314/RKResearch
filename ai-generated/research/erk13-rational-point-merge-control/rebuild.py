#!/usr/bin/env python3
"""Reoptimize the actual cubic prefix to make one physical same-clock merge."""
from functools import lru_cache
from fractions import Fraction as F
from itertools import permutations
from math import prod, lcm
from pathlib import Path
import argparse,json

def dot(a,b):return sum(x*y for x,y in zip(a,b))
def poly(roots):
    out=[F(1)]
    for t in roots:
        v=[F(0)]*(len(out)+1)
        for j,c in enumerate(out):v[j]-=t*c;v[j+1]+=c
        out=v
    return out
def ev(p,x):return sum(a*x**j for j,a in enumerate(p))
def J_at(p,x):return sum(a*x**(j+1)/(j+1)for j,a in enumerate(p))
def L(nodes,i):
    p=poly([x for j,x in enumerate(nodes)if j!=i])
    return [a/ev(p,nodes[i]) for a in p]
@lru_cache(None)
def forest(n,lo=(0,())):
    if not n:return ((),)
    return tuple((t,)+v for k in range(max(1,lo[0]),n+1)
                 for t in forest(k-1) if (k,t)>=lo for v in forest(n-k,(k,t)))
@lru_cache(None)
def size(t):return 1+sum(map(size,t))
@lru_cache(None)
def fac(t):return size(t)*prod(fac(x)for x in t)

def read(source):
    s=json.loads(source.read_text());A=[[F(x)for x in r]+[F(0)]*(14-i)for i,r in enumerate(s['A'])]
    b=list(map(F,s['b']))
    return A,b
def build(source):
    base,b=read(source)
    nodes=[sum(v)for v in base[6:]]
    B=[r[6:]for r in base[6:]]
    r=F(4,5);p=2*r/5;q=7*r/8;e=F(1,10);s=2*p/3
    c=[F(0),e,s,p,q,r]
    f=(r**3/3-p*r*r/2)/(q*(q-p))
    assert (p+q)*r**3/3-p*q*r*r/2==r**4/4
    A=[[],[e],[s-s*s/(2*e),s*s/(2*e)],[p/4,F(0),3*p/4]]
    def oldrow(t,z):
        u,v=t*t/2-z*q,t**3/3-z*q*q
        S=(p*u-v)/(s*(p-s));P=(v-s*u)/(p*(p-s))
        return [t-S-P-z,F(0),S,P]+([z]if z else [])
    A += [oldrow(q,F(0)),oldrow(r,f)]
    assert A[-1][2]==0 and dot(A[-1],[t**3 for t in c])==r**4/4
    pi=[[F(0)]*6 for _ in range(4)]
    for i,pos in enumerate([0,3,4,5]):
        for k,w in enumerate(L([F(0),p,q,r],i)):pi[k][pos]=w
    A=[r0+[F(0)]*(14-len(r0))for r0 in A]
    for i,t in enumerate(nodes):
        z=[t**(k+1)/(k+1)-dot(B[i],[x**k for x in nodes])for k in range(4)]
        A.append([dot(z,[pi[k][j]for k in range(4)])for j in range(6)]+B[i])
    merge=7;keep=5
    assert sum(A[merge])==r and A[merge]==A[keep]
    for row in A:
        row[keep]+=row[merge]
        del row[merge]
    del A[merge]
    b[keep]+=b[merge];del b[merge]
    assert len(A)==13 and len(set(map(tuple,A)))==13
    assert all(v==0 for i,row in enumerate(A) for v in row[i:])
    return A,b,[p,q,r,e],f
def check(A,b):
    n=len(A);c=[sum(r)for r in A]
    D=lcm(*(x.denominator for r in A for x in r),*(x.denominator for x in b))
    M=[[int(D*v)for v in r]for r in A];w=[int(v*D) for v in b]
    @lru_cache(None)
    def stage(t):return tuple(prod(u[i]for u in map(action,t))for i in range(n))
    @lru_cache(None)
    def action(t):
        V=stage(t)
        return tuple(dot(r,V)for r in M)
    cnt=[]
    for p in range(1,10):
        k=0
        for t in forest(p-1):
            b0=fac(t)*dot(w,stage(t))-D**p
            if b0:k+=1
        cnt.append(k)
        assert not k if p<9 else k>0
    ts=()
    for _ in range(8):ts=(ts,)
    T=F(fac(ts)*dot(w,stage(ts)),D**9)-1
    print("physical 13; exact rooted failure counts by grade 1..9:",cnt)
    print("degree-eight scalar exactness; ninth tall defect:",T)
    assert all(dot(b,[x**k for x in c])==F(1,k+1)for k in range(9))
    return T

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('--emit',type=Path);args=p.parse_args()
    A,b,c,f=build(args.source);T=check(A,b)
    print("Prefix changed to p,q,r,e:",*[str(x)for x in c],"third donor tap",f)
    out=json.dumps({"A":[list(map(str,r[:i]))for i,r in enumerate(A)],"b":list(map(str,b)),
                    "prefix":[str(x)for x in c],"f":str(f),"ninth_tall_defect":str(T)},indent=2)+"\n"
    if args.emit:args.emit.write_text(out)
    else:assert out==Path(__file__).with_name("tableau.json").read_text()
