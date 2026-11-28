#!/usr/bin/env python3
"""Standalone exact two-node pencil, weighted remainder, and physical old bank."""
from fractions import Fraction as Q
from itertools import combinations
from math import gcd, factorial, prod
def mul(p,q):
    r=[Q(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):r[i+j]+=a*b
    return tuple(r)
def poly(zeros):
    p=(Q(1),)
    for y in zeros:p=mul(p,(-y,Q(1)))
    return p
def val(p,x):
    r=Q(0)
    for a in p[::-1]:r=r*x+a
    return r
def prim(p):return (Q(0),)+tuple(a/(i+1) for i,a in enumerate(p))
def integra(p):return val(prim(p),Q(1))
def card(xs):
    return tuple(tuple(a/prod(x-y for y in xs if y!=x)
              for a in poly(tuple(y for y in xs if y!=x))) for x in xs)
def unpaid(d):
    if d==0:return 0
    while (s:=gcd(d,factorial(12)))>1:d//=s
    return abs(d)
def paid(a):return unpaid(a.denominator)==1
def unit(a):return paid(a) and unpaid(a.numerator)==1
weight=(Q(0),Q(1),Q(-3),Q(3),Q(-1))
R=tuple(map(Q,('1/4','1/3','1/2','2/3','5/6')))
seed=tuple(sorted((*R,Q(1,12),Q(3,4))))
assert not integra(mul(weight,poly(seed)))
m=[integra((Q(0),)*j+mul(weight,poly(R))) for j in range(3)]
assert m==list(map(Q,('-1/15120','-23/3991680','-1/1496880')))
D=m[1]**2-m[0]*m[2]
assert D==Q(-1,91048624128) and unit(D)
q=Q(1,18); t=(m[2]-q*m[1])/(m[1]-q*m[0])
assert t==Q(1,6)
C=tuple(sorted((*R,q,t)))
assert not integra(mul(weight,poly(C)))
delta=[-integra(mul(weight,L))/(6*x) for x,L in zip(C,card(C),strict=True)]
assert delta==list(map(Q,('-59049/4743200','-15/1232','-256/121275','-117/15400',
                         '-391/110880','-87/84700','-27/215600')))
assert all(map(paid,delta))
assert all(sum(x**j*d for x,d in zip(C,delta,strict=True))==
           -Q(1,prod(j+i for i in range(1,5))) for j in range(1,9))
assert [(x,y,unpaid((x-y).numerator)) for x,y in combinations((Q(0),*C,Q(1)),2)
        if not unit(x-y)]==[(Q(1,18),Q(1),17)]
assert any(unit(x) for x in delta) and unit(delta[0]) and unit(delta[1])
print('new 7-site, non-AP nodal integral and eight paid moments: exact')
print('only unpaid base gap:',1-C[0])
print('unit delta positions:',[str(x) for x,d in zip(C,delta,strict=True) if unit(d)])

# Physical old forward bank, independent small rooted enumeration.
c=list(map(Q,('0','1/40','1/20','1/10','1/24','1/8','1/4','3/8','1/2','1/3')))
P=(0,5,6,7,8,9)
donor=((),(0,1),(0,1,2),(0,2,3),(0,2,3,4),(0,3,4,5),
       (0,3,4,5,6),(0,3,4,5,7),(0,5,6,7,8),P)
A=[[Q(0)]*10 for _ in c]
for i in range(1,10):
    for j,L in zip(donor[i],card(tuple(c[k] for k in donor[i])),strict=True):
        A[i][j]=val(prim(L),c[i])
assert all(paid(a) for row in A for a in row)
def replay(A):
    F=[]
    for k in range(1,8):
        new=[]
        def rec(n,i,d,f):
            if n==0:
                new.append((k,k*d,f,[sum(b*a for a,b in zip(f,row,strict=True)) for row in A]))
                return
            for j in range(i,len(F)):
                m,c,y,z=F[j]
                if m>n:break
                rec(n-m,j,d*c,[u*v for u,v in zip(f,z,strict=True)])
        rec(k-1,0,1,[Q(1)]*10)
        assert len(new)==(1,1,2,4,9,20,48)[k-1]
        F.extend(new)
    return F
F=replay(A)
for n,g,v,_ in F:
    assert all(v[i]==Q(n,g)*c[i]**(n-1) for i in (P if n<=6 else (8,9)))
L=card(tuple(c[i] for i in P))
assert all(paid(a) for L0 in L for a in L0)
sig=A[6][:]
for i,ell in zip(P,L,strict=True):sig[i]-=val(prim(ell),c[6])
assert all(paid(s) for s in sig) and any(sig)
assert all(sum(s*x for s,x in zip(sig,v,strict=True))==0 for n,g,v,_ in F if n<=5)
mu=Q(-1024,243)
A[9]=[a+mu*s for a,s in zip(A[9],sig,strict=True)]
assert sum(A[9])==c[9] and all(paid(a) for a in A[9])
K={}
for n,g,v,_ in replay(A):
    if n<=6:
        assert all(v[i]==Q(n,g)*c[i]**(n-1) for i in P)
        continue
    r=[-sum(v[i]*ell[j] for i,ell in zip(P,L,strict=True)) for j in range(6)]+[Q(n,g)]
    assert val(r,Q(0))==val(r,Q(1,2))==0
    assert val(r,Q(1,3))==mu*val(r,Q(1,4))
    for j in sorted(K):
        if r[j]:r=[a-r[j]*b for a,b in zip(r,K[j],strict=True)]
    j=next((i for i,a in enumerate(r) if a),None)
    if j is not None:K[j]=[a/r[j] for a in r]
assert len(K)==4
print('paid literal old prefix, genuine size-six ports, and corrected size-seven rank-four band: exact')
