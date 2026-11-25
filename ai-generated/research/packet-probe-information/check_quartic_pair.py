#!/usr/bin/env python3
"""Exact coordinate check of the all-orders indistinguishable quartic ERK pair."""
from fractions import Fraction as F
from math import prod
from check_exact import all_trees,trees_up_to,dot


def poly_product(roots):
    coeff=[F(1)]
    for w in roots:
        new=[F(0)]*(len(coeff)+1)
        for j,z in enumerate(coeff):new[j]-=w*z;new[j+1]+=z
        coeff=new
    return coeff

def integ(coeff,x):return sum(z*x**(j+1)/(j+1) for j,z in enumerate(coeff))


def build(p,variant):
    L=p+1;xstar=F(1,2);z=F(5,8);y=F(3,4)
    X=[F(1,8),F(1,4),F(3,8),xstar,z]+[F(j,4*L+3) for j in range(1,L-4)]
    assert len(X)==len(set(X))==L
    roots=[F(0)]+X[:3];coeff=poly_product(roots);P=lambda x:prod(x-r for r in roots)
    A=[{}];b=[F(0)];c=[F(0)]
    def row(D,x):
        assert sum(D.values(),F(0))==x and all(0<=j<len(A) for j in D)
        A.append({j:v for j,v in D.items() if v});c.append(x);b.append(F(0));return len(A)-1
    U=[row({0:x},x) for x in X]
    prev=[]
    for x in X:
        J=integ(coeff,x)
        a=J*(z-x)/((z-xstar)*P(xstar));q=J*(x-xstar)/((z-xstar)*P(z))
        prev.append(row({0:x-a-q,U[3]:a,U[4]:q},x))
    lag=[]
    for k,x in enumerate(X):
        others=X[:k]+X[k+1:];Lk=poly_product(others);den=prod(x-u for u in others)
        lag.append([a/den for a in Lk])
    B=[[integ(f,x) for f in lag] for x in X]
    for r in range(p+1):
        assert all(sum(z*x**r for z,x in zip(rr,X))==y**(r+1)/(r+1) for rr,y in zip(B,X))
    for depth in range(p-1):
        fresh=[row(dict(zip(prev,q)),x) for q,x in zip(B,X)];prev=fresh
    for j,f in zip(prev,lag):b[j]=integ(f,F(1))-f[p]/(p+1)
    assert sum(b[j]*c[j]**p for j in prev)==0
    tail=[]
    for sign in (1,-1):
        j=row({U[3] if variant else 0:y},y);tail.append(j);b[j]=F(sign)
    # Retain every original stage and prefix. Append all clones at the end.
    for j in range(len(A)):
        if not b[j]:
            k=row(A[j].copy(),c[j]);b[j]=F(1);b[k]=F(-1)
    assert all(b) and c[:4]==roots and len(c)==len(b)==len(A)
    return A,tuple(b),tuple(c),tail,P


def case(p):
    pairs=[build(p,i) for i in (0,1)]
    assert pairs[0][1:4]==pairs[1][1:4]
    ts,ns,gs=trees_up_to(min(8,p))
    roots=pairs[0][2][:4];vnorm=[]
    for variant,(rows,b,c,tail,P) in enumerate(pairs):
        A=lambda x:tuple(sum((v*x[j] for j,v in r.items()),F(0)) for r in rows)
        assert A((F(1),)*len(c))==c
        q=tuple(P(x) for x in c);ap=A(q);acp=A([x*y for x,y in zip(c,q)]);aap=A(ap)
        v=tuple(x*y-z-u for x,y,z,u in zip(c,ap,acp,aap))
        assert all(v[j]==(variant*F(9,8192) if j in tail else 0) for j in range(len(v)))
        assert sum((ww*x)**2 for ww,x in zip(b,v))==variant*F(81,33554432)
        assert dot(b,[x*x for x in v])==0
        assert all(dot(b,[x**j for x in c])==F(1,j+1) for j in range(p))
        assert dot(b,[x**p for x in c])==0
        if p<=8:
            V,_=all_trees(A,b,ts)
            assert all(dot(b,x)*g==1 for x,g in zip(V,gs))
    A0,A1=pairs[0][0],pairs[1][0]
    assert len(A0)==len(A1) and {j for j in range(len(A0)) if A0[j]!=A1[j]}==set(tail)
    assert A0[tail[0]]==A0[tail[1]] and A1[tail[0]]==A1[tail[1]]
    assert all(not (set(r)&set(tail)) for r in A0+A1)
    print(f'p={p}, size={len(c)}, same b,c and all individual weights nonzero; genuine first-four-stage quartic cut. Exact moments through {p-1}, bush moment at degree {p}=0 instead of 1/{p+1}; T(P) differs only at two cancelled nonzero weights, 0 versus 9/8192. b^2-Gram 0 versus 81/33554432. F0 step loses 1 versus 0. '+(f'All {len(ts)} rooted trees through order {p} evaluated on both tables.' if p<=8 else 'Polynomial integration panel identities checked for every degree 0..20; all-tree conclusion by the panel induction.'))

if __name__=='__main__':case(8);case(20)
