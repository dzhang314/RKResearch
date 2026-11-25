#!/usr/bin/env python3
"""Exact corroboration on endpoint-power specializations, not node search."""
from fractions import Fraction as F
from math import prod


def need(x,m):
    if not x: raise AssertionError(m)


def add(a,b):
    return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0)
            for i in range(max(len(a),len(b)))]


def scale(a,b):
    return [x*b for x in a]


def mul(a,b):
    out=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            out[i+j]+=x*y
    return out


def ev(a,x):
    v=F(0)
    for y in a[::-1]: v=v*x+y
    return v


def trim(a):
    a=list(map(F,a))
    while a and not a[-1]:
        a.pop()
    return a


def rem(a,b):
    a=trim(a)
    b=trim(b)
    while a and len(a)>=len(b):
        j=len(a)-len(b)
        q=a[-1]/b[-1]
        for i,x in enumerate(b):
            a[i+j]-=q*x
        a=trim(a)
    return a


def deriv(a):
    return [i*a[i] for i in range(1,len(a))]


def squarefree(a):
    a,b=trim(a),trim(deriv(a))
    while b: a,b=b,rem(a,b)
    return len(a)==1


def solve(A,b):
    n=len(A)
    D=[list(map(F,x))+[F(y)] for x,y in zip(A,b)]
    for i in range(n):
        k=next(k for k in range(i,n) if D[k][i])
        D[i],D[k]=D[k],D[i]
        v=D[i][i]
        D[i]=[x/v for x in D[i]]
        for j in range(n):
            if j!=i:
                v=D[j][i]
                D[j]=[a-v*b for a,b in zip(D[j],D[i])]
    return [v[-1] for v in D]


def det(M):
    M=[list(map(F,r)) for r in M]
    n=len(M)
    d=F(1)
    for i in range(n):
        k=next((k for k in range(i,n) if M[k][i]),None)
        if k is None: return F(0)
        if k!=i:
            M[i],M[k]=M[k],M[i]
            d=-d
        b=M[i][i]
        d*=b
        for j in range(i+1,n):
            q=M[j][i]/b
            M[j]=[u-q*v for u,v in zip(M[j],M[i])]
    return d


def discr(a):
    # Monic polynomial; Sylvester sign is paid by standard discriminant.
    a=a[::-1]
    b=deriv(a[::-1])[::-1]
    nr,ns=len(a)-1,len(b)-1
    rows=[]
    for s,c in ((ns,a),(nr,b)):
        for i in range(s):
            rows.append([0]*i+c+[0]*(s-i-1))
    return (-1)**(nr*(nr-1)//2)*det(rows)


def from_values(vals):
    n=len(vals)
    S=[0]
    for i,y in enumerate(vals):
        z=[j for j in range(n) if j!=i]
        l=[F(1)]
        for j in z: l=mul(l,[-j,1])
        S=add(S,scale(l,y/prod(i-j for j in z)))
    return S


def pencil(k,t):
    # Prefix H=X^k, potentially repeated; only a specialization witness
    # for the good open, not a physical quadrature candidate.
    def mu(i): return F(1,k+i+1)
    M=[[mu(i+j) for j in range(t)] for i in range(t)]
    A=solve(M,[-mu(i+t+1) for i in range(t)])+[F(0),F(1)]
    B=solve(M,[-mu(i+t) for i in range(t)])+[F(1)]
    for f in (A,B):
        need(all(sum(c*mu(i+j) for j,c in enumerate(f))==0 for i in range(t)),
             "all weighted pencil moments")
    return A,B


for t in (2,3):
    last=20-2*t-1
    for k in range(last+1):
        A,B=pencil(k,t)
        n=t+1
        d=2*n-2
        g=lambda s:add(A,scale(B,F(s)))
        delta=from_values([discr(g(j)) for j in range(d+1)])
        need(len(trim(delta))==d+1 and squarefree(delta)
             and ev(delta,d+1)==discr(g(d+1)),("simple pencil branches",k,t))
        if t==2:
            D=add(add(mul(A,A),mul([4*B[1],2],mul(A,B))),
                  scale(mul([4*A[1],0,3],mul(B,B)),-1))
            need(len(trim(D))==5 and squarefree(D),"good quartic on pointed-root line")
            for a in (F(-1),F(0),F(1)):
                need(ev(B,a)!=0,"test finite parameter")
                lam=-ev(A,a)/ev(B,a)
                G=g(lam)
                q=[a*a+a*lam+G[1],a+lam,F(1)]
                need(mul(q,[-a,1])==G and ev(D,a)==discr(q)*ev(B,a)**2,
                     "literal rational-root/discriminant identity")
    print(f"t={t}: all endpoint exponents 0..{last} through p=20 have "
          f"{d} simple pencil branch parameters in the exact discriminant.")
print("PASS: weighted specializations only; no search for rational quadrature nodes.")
