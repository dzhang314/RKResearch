#!/usr/bin/env python3
"""Independent exact replay for the fixed-block obstruction."""
from argparse import ArgumentParser
from functools import cache
from fractions import Fraction as F
from math import factorial, lcm, prod
from pathlib import Path
import json

R=Path(__file__).parent

def freeze(t):
    return tuple(map(freeze,t))

@cache
def grade(t):
    return 1+sum(map(grade,t))

@cache
def tfact(t):
    return grade(t)*prod(map(tfact,t))

def mv(A,v):
    return tuple(sum(a*x for a,x in zip(row,v) if a and x)for row in A)

def phi_spine(A,c,t,p):
    tail=tuple(u for u in t if u)
    assert len(tail)<=1
    ls=len(t)-len(tail)
    raw=tuple(pow(x,ls,p)for x in c)
    if not tail:
        return raw
    v=mv(A,phi_spine(A,c,tail[0],p))
    return tuple(x*y%p for x,y in zip(raw,v))

def mod(x,p):
    return x.numerator*pow(x.denominator,-1,p)%p

def dot(u,v):
    return sum(x*y for x,y in zip(u,v)if x and y)

@cache
def forests(n,lo=(1,())):
    if n==0:return ((),)
    return tuple((u,)+v for j in range(lo[0],n+1)for u in forests(j-1)
                 if (j,u)>=lo for v in forests(n-j,(j,u)))

def check_rational(A,b,D):
    I=[tuple(int(D*x)for x in row)for row in A]
    w=tuple(int(D*x)for x in b)
    assert all(F(y,D)==x for row,ri in zip(A,I)for x,y in zip(row,ri))
    assert all(F(y,D)==x for x,y in zip(b,w))
    N=len(b)
    @cache
    def phi(t):
        act=[action(s)for s in t]
        return tuple(prod(u[i]for u in act)for i in range(N))
    @cache
    def action(t):return mv(I,phi(t))
    counts=[]
    for n in range(1,12):
        terms=forests(n-1)
        assert all(tfact(t)*dot(w,phi(t))==D**n for t in terms)
        counts.append(len(terms))
    assert counts==[1,1,2,4,9,20,48,115,286,719,1842]
    t=((),)*11
    defect=F(tfact(t)*dot(w,phi(t)),D**12)-1
    assert defect==F(1,165)
    print("Candidate:",N,"stages,",sum(counts),"tree conditions; order-twelve unit defect",defect)

def audit(full):
    x=json.loads((R/"tableau.json").read_text())
    r=json.loads((R/"dual-mod13.json").read_text())
    p,h,j=r["prime"],r["cut"],r["remove"]
    n=len(x["A"]);assert (p,n,h,j)==(13,22,16,11)
    B=[list(map(F,row))+[F(0)]*(n-i)for i,row in enumerate(x["A"])]
    b=list(map(F,x["b"]))
    D=lcm(*(a.denominator for row in B for a in row),*(w.denominator for w in b))
    assert D==398337730560000 and factorial(11)**3%D==0
    assert all(len(x["A"][i])==i for i in range(n))
    assert b[j]==0 and sum(B[j])==F(-1,3)
    assert not any(B[i][j]for i in range(h))
    if full:check_rational(B,b,D)
    A=[[mod(z,p)for z in row]for row in B]
    w=[mod(z,p)for z in b];c=tuple(sum(row)%p for row in A)
    for i in range(h,n):
        A[i][0]=(A[i][0]+A[i][j])%p
        A[i][j]=0
    assert tuple(sum(row)%p for row in A)==c
    names=[(i,k)for i in range(h,n)for k in range(1,h)if k!=j]
    keep=[k for k in range(n)if k!=j]
    assert len(names)==84 and len(keep)==21
    expanded=len(keep)+sum(n-i for i,k in names)
    assert r["numVars"]==expanded==315
    terms=[(a,freeze(t))for a,t in r["terms"]]
    assert len(terms)==141 and len(set(t for _,t in terms))==141
    assert all(0<a<p and grade(t)<=11 for a,t in terms)
    T=sum(a*pow(tfact(t),-1,p)for a,t in terms)%p
    assert T==1
    def vectorsum():
        tot=[0]*len(keep)
        for a,t in terms:
            v=phi_spine(A,c,t,p)
            for j,k in enumerate(keep):
                tot[j]=(tot[j]+a*v[k])%p
        return tot
    assert not any(vectorsum())
    for i,k in names:
        A[i][k]+=1
        A[i][0]-=1
        assert not any(vectorsum())
        A[i][k]-=1
        A[i][0]+=1
    print("Modulo",p,"dual receipt:",len(terms),"rooted conditions,",len(names),
          "matrix directions,",len(keep),"output coordinates; contradiction",T)

if __name__=="__main__":
    p=ArgumentParser()
    p.add_argument("--full",action="store_true")
    audit(p.parse_args().full)
