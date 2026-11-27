#!/usr/bin/env python3
"""Exact literal first ghost and its next off-old scalar gate."""
from fractions import Fraction as F
from functools import lru_cache
from math import prod
from pathlib import Path
from itertools import combinations
import argparse,json

def poly(roots):
    p=[F(1)]
    for r in roots:
        v=[F(0)]*(len(p)+1)
        for i,a in enumerate(p):
            v[i]-=r*a;v[i+1]+=a
        p=v
    return p
def ev(p,x):return sum(a*x**k for k,a in enumerate(p))
def integral(p,x):return sum(a*x**(k+1)/(k+1)for k,a in enumerate(p))
def dot(u,v):return sum(a*b for a,b in zip(u,v))
def lagrange(nodes,j):
    p=poly([v for k,v in enumerate(nodes)if k!=j])
    w=ev(p,nodes[j])
    return [a/w for a in p]
@lru_cache(None)
def forest(n,lo=(0,())):
    if n==0:return ((),)
    return tuple((u,)+v for k in range(max(lo[0],1),n+1)
                 for u in forest(k-1) if (k,u)>=lo for v in forest(n-k,(k,u)))
@lru_cache(None)
def size(t):return 1+sum(map(size,t))
@lru_cache(None)
def fac(t):return size(t)*prod(map(fac,t))

def make():
    p,e=F(1),F(1,7);r=F(3,4);q=r*(5-3*r)/(10-5*r);f=F(65625,63382);s=2*p/3
    clock=[F(0),e,s,p,q,r,r]
    A=[[],[e],[s-s*s/(2*e),s*s/(2*e)],[p/4,F(0),3*p/4]]
    def oldrow(t,w):
        v1,v2=t*t/2-w*q,t**3/3-w*q*q
        a=(p*v1-v2)/(s*(p-s));b=(v2-s*v1)/(p*(p-s))
        return [t-a-b-w,F(0),a,b]+([w] if w else [])
    A.extend([oldrow(q,F(0)),oldrow(r,f)])
    model=[F(0),p,q,r]
    ell0=[integral(lagrange(model,i),r)for i in range(4)]
    assert integral(poly(model),r)==0
    J=[ell0[0],F(0),F(0),*ell0[1:]]
    mix=[(a+b)/2 for a,b in zip(A[5]+[F(0)],J)]
    A.append(mix)
    Q=[dot(A[i],[v**3 for v in clock])-clock[i]**4/4 for i in (3,4,5)]
    V=[A[i][2]for i in (3,4,5)]
    assert dot(ell0[1:],Q)==dot(ell0[1:],V)==0
    assert all(ell0[i]for i in (1,2,3)) and Q[2] and V[2]
    assert mix!=A[5]+[0] and mix!=J
    @lru_cache(None)
    def P(t):
        return [prod(v[i]for v in map(Act,t))for i in range(8)]
    @lru_cache(None)
    def Act(t):
        v=P(t)
        return [dot(a,v)for a in A+[J]]
    checked=0
    for n in range(1,7):
        for t in forest(n-1):
            G=F(n,fac(t))*r**(n-1)
            V0=P(t)
            assert V0[7]==G and V0[6]==(V0[5]+G)/2
            checked+=1
    assert checked==37
    print("37 actual rooted profiles through size six: locally pure model available; marked first high gives exact half old defect.")
    print("Nonzero physical old grade-four defects at r:",V[2],Q[2])
    return {"A":[list(map(str,row))for row in A],"clock":list(map(str,clock)),
            "q":str(q),"r":str(r),"f":str(f),"JrPi":list(map(str,J)),
            "old_donor_evaluation":list(map(str,ell0[1:]))}

def gate():
    from sympy import Matrix, Rational, Symbol, cancel, prod
    z=Symbol("z")
    p,q,r=1,Rational(33,100),Rational(3,4)
    ell=list(map(Rational,("-81/4288","78125/165088","43/224")))
    J=lambda x:[x**(i+1)/(i+1)for i in range(1,5)]
    E=[r**i for i in range(1,5)]
    clocks=[p,q,r]
    L=[sum(l*c**(i+1)/(i+1)*prod(d-z for d in clocks if d!=c)
           for c,l in zip(clocks,ell))for i in range(1,5)]
    pol=Matrix([J(r),E,L,J(z)]).det(method="domain-ge")
    expected=2187*z**2*(z-1)*(4*z-3)**3*(100*z-33)/671088640000
    assert cancel(pol-expected)==0
    print("Exact second distinct off-old Cramer determinant has only forbidden/old-clock roots.")

if __name__=="__main__":
    pp=argparse.ArgumentParser();pp.add_argument("--emit",type=Path);args=pp.parse_args()
    o=json.dumps(make(),indent=2)+"\n"
    if args.emit:args.emit.write_text(o)
    else:assert o==Path(__file__).with_name("port.json").read_text()
    gate()
