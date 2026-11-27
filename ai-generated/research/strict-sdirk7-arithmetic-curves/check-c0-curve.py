#!/usr/bin/env python3
"""Exact bidegree-(26,21) c=0 clock projection and rational-point tests."""
from flint import fmpz_mpoly_ctx, fmpz_poly, fmpq, fmpq_poly, nmod_poly
from itertools import combinations
from math import prod, gcd, isqrt
from fractions import Fraction
from pathlib import Path
import argparse
import json
import sympy as S


def chart_polynomials(u,z,s):
    one,zero=s**0,0*s
    def add(f,g):
        a=[zero]*max(len(f),len(g))
        for i,v in enumerate(f): a[i]+=v
        for i,v in enumerate(g): a[i]+=v
        while len(a)>1 and not a[-1]:a.pop()
        return a
    def scal(f,v):
        return [a*v for a in f]
    def mul(f,g):
        a=[zero]*(len(f)+len(g)-1)
        for i,b in enumerate(f):
            for j,c in enumerate(g): a[i+j]+=b*c
        return a
    def hull(ys):
        a=[one]
        for y in ys:
            a=mul(a,[-y,one])
        return a
    def moment(P,j=0):
        return sum(a*(420//(i+j+1))*z**(i+j) for i,a in enumerate(P))

    v=2*u-1
    c=zero
    Y=[one,u,v,c]
    R4=hull(Y)
    A=[moment(R4,i) for i in range(3)]
    Q=[s*A[1]-A[2],-s*A[0],A[0]]
    M=u*u-4*u+2
    T=u**3-7*u*u+10*u-2
    J=4*u**3-24*u*u+39*u-17
    q0=2*(u-2)*(u-1)**2
    q1=-2*(u-3)*(u-1)*(2*u-3)
    q2=(u-3)*(u-2)**2
    G=6*q0*(c-1)+3*q1*(c*c-2*c)+2*q2*(c**3-3*c*c)
    E=-6*M*q1+q2*(-8*M+4*(1-M)*(c-1))-12*T*(1-c)
    rate=[-T*E,M*T*E,M*J*E,-2*T*M*G]
    hull3=[hull(Y[:i]+Y[i+1:]) for i in range(4)]
    K=[moment(mul(Q,S)) for S in hull3]
    L=[r*k for r,k in zip(rate,K)]
    Gd=L[0]-2*L[1]+L[2]
    Gn=L[0]-2*u*L[1]+v*L[2]
    F=Gd*((u-1)*c*L[3]-(u-c)*L[0]-(c-1)*u*L[1])-Gn*((u-1)*L[3]-(u-c)*L[0]-(c-1)*L[1])
    V=prod(Y[j]-Y[i] for i,j in combinations(range(4),2))
    W=add(scal([u,-one],(Gd-Gn)*L[0]),scal([-one,one],(Gd*u-Gn)*L[1]))
    UR=[zero]
    for i,y in enumerate(Y):
        scale=(-1)**(3-i)*prod(Y[b]-Y[a] for a,b in combinations(range(4),2) if i not in (a,b))
        UR=add(UR,scal(hull3[i],scale*(u-1)**2*(Gd*y-Gn)**2*rate[i]**2*K[i]))
    KR=[A[0]*(A[1]-s*A[0]),A[0]**2]

    def rem(P):
        while len(P)>2:
            n=len(P)-1
            P=add(scal(P,A[0]),[zero]*(n-2)+scal(Q,-P[-1]))
        assert len(P)==2
        return P

    d=rem(mul(KR,R4))
    n=rem(add(scal(mul(W,W),V),scal(mul(KR,UR),-one)))
    Phi=d[0]*n[1]-d[1]*n[0]
    return F,Phi,A

def load():
    rows=json.loads(Path(__file__).with_name("c0-projected-h.json").read_text())
    assert all(k==0 for (i,j,k),val in rows)
    terms={(i,j):int(val) for (i,j,k),val in rows}
    assert len(terms)==567
    assert max(i for i,j in terms)==26 and max(j for i,j in terms)==21
    return terms


def rebuild(terms):
    R=fmpz_mpoly_ctx.get(('u','z','s'),'lex')
    F,Phi,_=chart_polynomials(*R.gens())
    assert F.degrees()==(25,18,2) and Phi.degrees()==(75,79,6)
    Res=F.resultant(Phi,2)
    content,factors=Res.factor()
    assert Res==content*prod(g**e for g,e in factors)
    assert len(factors)==14
    chosen=[(g,e) for g,e in factors if int(g(4,8,5))%19==0]
    assert len(chosen)==1
    h,e=chosen[0]
    assert e==1 and h.degrees()==(26,21,0)
    assert h==R.from_dict({(i,j,0):a for (i,j),a in terms.items()})


def project_u(terms,u):
    result=[0]*22
    a,b=u.numerator,u.denominator
    for (i,j),f in terms.items():
        result[j]+=f*a**i*b**(26-i)
    return fmpz_poly(result)


def project_z(terms,z):
    result=[0]*27
    a,b=z.numerator,z.denominator
    for (i,j),f in terms.items():
        result[i]+=f*a**j*b**(21-j)
    return fmpz_poly(result)


def prime_eval(q,p=19):
    return q.numerator*pow(q.denominator,-1,p)%p


def simple_checks(terms):
    f=nmod_poly(project_u(terms,Fraction(4)).coeffs(),23)
    assert f.degree()==21 and all(f(t) for t in range(23))
    f=nmod_poly(project_z(terms,Fraction(8)).coeffs(),13)
    assert f.degree()==26 and all(f(t) for t in range(13))
    K=19
    s=nmod_poly([0,1],K)
    F,Phi,A=chart_polynomials(nmod_poly([4],K),nmod_poly([8],K),s)
    rem=Phi%F
    assert F.degree()==2 and rem.degree()==1
    assert F(5)==rem(5)==0
    assert all(a.degree()<=0 for a in A)
    p=(5*int(A[1][0])-int(A[2][0]))*pow(int(A[0][0]),-1,19)%19
    assert p==2 and (25-4*p)%19==17
    eu=sum(a*i*pow(4,i-1,19)*pow(8,j,19) for (i,j),a in terms.items() if i)%19
    ez=sum(a*j*pow(4,i,19)*pow(8,j-1,19) for (i,j),a in terms.items() if j)%19
    assert (eu,ez)==(12,9)
    print("Selected c=0 chart: rootless rational u=4 and z=8 fibers; finite linear recovery.")


def rational_check(terms,u,z):
    assert prime_eval(u)==4 and prime_eval(z)==8
    poly=project_u(terms,u)
    coeff=[int(q) for q in poly.coeffs()]
    v=sum(a*z.numerator**j*z.denominator**(21-j) for j,a in enumerate(coeff))
    if v:
        return None
    def fq(q):
        return fmpq(q.numerator,q.denominator)
    F,Phi,A=chart_polynomials(fmpq_poly([fq(u)]),fmpq_poly([fq(z)]),fmpq_poly([0,1]))
    rem=Phi%F
    assert F.degree()==2 and rem.degree()==1
    s=-Fraction(str(rem[0]))/Fraction(str(rem[1]))
    assert prime_eval(s)==5 and not F(fq(s)) and not Phi(fq(s))
    a0,a1,a2=(Fraction(str(a[0])) for a in A)
    p=(s*a1-a2)/a0
    disc=s*s-4*p
    result=dict(s=str(s),p=str(p),disc=str(disc))
    if disc<0:
        return result
    a,b=isqrt(disc.numerator),isqrt(disc.denominator)
    if (a*a,b*b)!=(disc.numerator,disc.denominator):
        return result
    a,b=(s+Fraction(a,b))/2,(s-Fraction(a,b))/2
    if prime_eval(a)==15:
        a,b=b,a
    assert prime_eval(a)==9 and prime_eval(b)==15
    return result|dict(a=str(a),b=str(b))


def sieve(terms,height):
    # For each reduced u of this height and selected residue, check every
    # rational z, without bounding z: projective prime sieves, then exact
    # integer polynomial factors and linear roots.
    primes=list(S.primerange(17,89))
    allowed={}
    for p in primes:
        allowed[p]=set()
        for u in range(p+1):
            f=(project_u(terms,Fraction(u)) if u<p else
               fmpz_poly([terms.get((26,j),0) for j in range(22)]))
            f=nmod_poly(f.coeffs(),p)
            if f.degree()!=21 or f.roots():
                allowed[p].add(u)
    seen=survivors=0
    candidates=[]
    for den in range(1,height+1):
        if den%19==0:
            continue
        for num in range(-height+(4*den+height)%19,height+1,19):
            assert num%19==4*den%19
            if gcd(num,den)!=1:
                continue
            seen+=1
            if any((num*pow(den,-1,p)%p if den%p else p) not in allowed[p]
                   for p in primes):
                continue
            survivors+=1
            u=Fraction(num,den)
            f=project_u(terms,u)
            assert f
            co,fs=f.factor()
            assert f==co*prod((g**e for g,e in fs),start=fmpz_poly([1]))
            for g,e in fs:
                if g.degree()==1:
                    z=Fraction(-int(g[0]),int(g[1]))
                    if z.denominator%19 and prime_eval(z)==8:
                        candidates.append((u,z,rational_check(terms,u,z)))
    print(f"Exact bounded-u diagnostic: {seen} eligible u; {survivors} factored; {len(candidates)} projected rational pairs.")
    for row in candidates:
        print(row)


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--rebuild",action="store_true")
    parser.add_argument("--height",type=int)
    parser.add_argument("--u",type=Fraction)
    parser.add_argument("--z",type=Fraction)
    args=parser.parse_args()
    terms=load()
    simple_checks(terms)
    if args.rebuild:
        rebuild(terms)
        print("Fraction-free resultant and selected integer factor verified.")
    if args.height:
        sieve(terms,args.height)
    if args.u is not None or args.z is not None:
        assert args.u is not None and args.z is not None
        q=rational_check(terms,args.u,args.z)
        print(q if q is not None else "The candidate is not on the selected projected curve.")
