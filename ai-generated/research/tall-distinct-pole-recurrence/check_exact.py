#!/usr/bin/env python3
"""Exact base-field gcd, finite recurrence, and repeated-pole families."""
from fractions import Fraction as F
from itertools import product
from math import factorial


def poly(v):
    v=list(map(F,v))
    while v and not v[-1]:
        v.pop()
    return tuple(v)


def coeff(a,i):
    return a[i] if 0<=i<len(a) else F(0)


def plus(a,b):
    return poly(coeff(a,i)+coeff(b,i) for i in range(max(len(a),len(b))))


def scale(a,c):
    return poly(c*x for x in a)


def mult(a,b):
    if not a or not b:
        return ()
    v=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            v[i+j]+=x*y
    return poly(v)


def powp(a,k):
    v=(F(1),)
    for _ in range(k):
        v=mult(v,a)
    return v


def der(a):
    return poly(i*x for i,x in enumerate(a) if i)


def divmodp(a,b):
    q=[F(0)]*max(0,len(a)-len(b)+1)
    while len(a)>=len(b):
        j=len(a)-len(b)
        c=a[-1]/b[-1]
        q[j]=c
        a=plus(a,(F(0),)*j+scale(b,-c))
    return poly(q),a


def gcd(a,b):
    while b:
        a,b=b,divmodp(a,b)[1]
    return scale(a,1/a[-1])


def mulcert(q):
    g=gcd(q,der(q))
    v,s=divmodp(q,g)
    b,t=divmodp(der(q),g)
    assert not s and not t and len(b)<len(v)
    assert v[0] and mult(v,der(q))==mult(b,q)
    return v,b


def ecoef(q,n):
    return sum(x/factorial(n-i) for i,x in enumerate(q[:n+1]))


def recurrence_checks(q,d):
    v,b=mulcert(q)
    assert len(v)==d+1
    K=len(q)+3
    es=[ecoef(q,j) for j in range(K+2)]
    assert es[0]==1
    w=plus(v,b)
    for k in range(K+1):
        inds=range(min(d,k)+1)
        assert sum(coeff(v,i)*(k-i+1)*es[k-i+1] for i in inds)==sum(
            coeff(w,i)*es[k-i] for i in inds)
        # Formal-series-free derivative residual, with exact cutoff.
        def residual(length):
            u=tuple(F(1,factorial(j)) for j in range(length))
            f=mult(q,u)
            left=plus(mult(v,der(f)),scale(mult(w,f),-1))
            right=mult(mult(v,q),plus(der(u),scale(u,-1)))
            assert left==right
            return left
        assert coeff(residual(k+2),k)==0
        assert coeff(residual(k+1),k)==-v[0]/factorial(k)
        # Polynomial-only forward identity has a shorter memory window.
        assert sum(coeff(v,i)*(k-i+1)*coeff(q,k-i+1) for i in inds)==sum(
            coeff(b,i)*coeff(q,k-i) for i in range(min(d-1,k)+1))
    assert all(any(es[j:j+d+1]) for j in range(len(es)-d))
    return K+1


# Pairwise-coprime linear and irreducible quadratic factors over Q.
factors=[poly(v) for v in ((1,2),(1,-3),(1,0,1),(1,1,1))]
assert all(len(gcd(a,b))==1 for i,a in enumerate(factors) for b in factors[i+1:])
checks=0
for profile in product(range(3),repeat=len(factors)):
    q=(F(1),)
    for f,k in zip(factors,profile):
        q=mult(q,powp(f,k))
    d=sum(len(f)-1 for f,k in zip(factors,profile) if k)
    checks+=recurrence_checks(q,d)
print(f'81 base-field gcd profiles, {checks} exact truncated residual/recurrence/one-short checks')

sharp=ledger=0
for d in range(1,10):
    for e in range(1,8):
        V=tuple(F((-1)**i,e**i*factorial(i)) for i in range(d+1))
        Q=powp(V,e)
        assert len(mulcert(Q)[0])==d+1 and len(Q)==e*d+1
        assert ecoef(Q,0)==1 and not any(ecoef(Q,n) for n in range(1,d+1))
        nextval= -e*F((-1)**(d+1),e**(d+1)*factorial(d+1))
        assert ecoef(Q,d+1)==nextval!=0
        sharp+=1
        if d<=4:
            # P=1. C either removes additional copies of retained roots,
            # or removes one separate real location as well.
            for C,delta in [(V,0),(poly([1,2,1]),1),(mult(powp(V,2),poly([1,2,1])),1)]:
                D=mult(C,Q)
                N=C
                physical_d=len(mulcert(D)[0])-1
                s=len(D)+1 # two physical zero modes
                c=len(C)-1
                r=len(Q)-1
                nu=s-(len(N)-1)
                z=s-(len(D)-1)
                assert physical_d-d==delta and d+c+nu+delta==s+physical_d
                assert d+2*c+z+nu+(r-d)==2*s
                ledger+=1
print(f'{sharp} explicit rational repeated-pole sharp families, {ledger} exact cancellation ledgers')
