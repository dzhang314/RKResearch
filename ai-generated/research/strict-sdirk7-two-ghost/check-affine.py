#!/usr/bin/env python3
from flint import fmpz_mpoly_ctx,fmpz_poly,nmod_poly
from itertools import combinations
from math import gcd,prod
from pathlib import Path
from sympy import primerange
from fractions import Fraction
import json,time
R=fmpz_mpoly_ctx.get(('u','z'),'lex')
u,z=R.gens()
one,zero=R.constant(1),R.constant(0)
def add(f,g):
    p=[zero]*max(len(f),len(g))
    for i,v in enumerate(f):p[i]+=v
    for i,v in enumerate(g):p[i]+=v
    while len(p)>1 and not p[-1]:p.pop()
    return p
def mul(f,g):
    p=[zero]*(len(f)+len(g)-1)
    for i,v in enumerate(f):
        for j,w in enumerate(g):p[i+j]+=v*w
    return p
def scale(f,s):return [v*s for v in f]
def hull(nodes):
    f=[one]
    for y in nodes:f=mul(f,[-y,one])
    return f
def mom(p,j=0):
    assert len(p)+j <= 7
    return sum(v*(420//(i+j+1))*z**(i+j) for i,v in enumerate(p))
def val(p,y):return sum(v*y**i for i,v in enumerate(p))

def build(pivots_only=False):
    a=z-1; v=2*u-1; c=zero
    M=u*u-4*u+2; T=u**3-7*u*u+10*u-2; J=4*u**3-24*u*u+39*u-17
    q0=2*(u-2)*(u-1)**2
    q1=-2*(u-3)*(u-1)*(2*u-3)
    q2=(u-3)*(u-2)**2
    G=-6*q0
    E=-6*M*q1+q2*(-8*M-4*(1-M))-12*T
    Y=[a,c,v,u,one]
    H=hull(Y)
    R5=[hull(Y[:i]+Y[i+1:]) for i in range(5)]
    A=[M*J*mom(R5[2],j)-2*M*T*mom(R5[3],j)-T*mom(R5[4],j) for j in range(3)]
    B=[2*(u-1)*M*G*mom(R5[1],j)-E*(u*mom(R5[4],j)+M*mom(R5[3],j)) for j in range(3)]
    D=A[1]*B[0]-A[0]*B[1]
    s=A[2]*B[0]-A[0]*B[2]
    p=A[2]*B[1]-A[1]*B[2]
    if pivots_only:return D,s,p
    Q=[p,-s,D]
    K=[mom(mul(f,Q)) for f in R5]
    W1=-T*K[4]; Wu=M*T*K[3]
    W=[u*W1-Wu,Wu-W1]
    dv=prod(Y[j]-Y[i] for i,j in combinations(range(5),2))
    Cprod=dv*prod(K)
    U4=[zero]
    for i,y in enumerate(Y):
        aux=(-1)**(4-i)*prod(Y[j]-Y[k] for k,j in combinations(range(5),2) if i not in (k,j))
        U4=add(U4,scale(R5[i],aux*val(W,y)**2*prod(k for j,k in enumerate(K) if i!=j)))
    remK=[D*mom(H,1)-s*mom(H),D*mom(H)]
    def rem(f):
        for i in range(7,1,-1):
            last=f[i] if i<len(f) else zero
            f=add(scale(f,D),[zero]*(i-2)+scale(Q,-last))
        return f+[zero]*(2-len(f))
    v0,v1=rem(mul(remK,H))
    w0,w1=rem([zero]+mul(remK,H))
    c0,c1=rem(add(scale(mul(W,W),Cprod),scale(mul(remK,U4),-one)))
    C=v0*w1-v1*w0
    N0=c0*w1-c1*w0
    N1=v0*c1-v1*c0
    F=D*N1*U4[4]*C-D*N0*N0-s*N0*N1-p*N1*N1
    bad=[z,dv,M,T,D,C,*K,*[val(Q,y) for y in Y],s*s-4*p*D]
    return F,bad,D,s,p

def univar(F,i):
    d=F.to_dict(); assert all(not e[1-i] for e in d)
    def k(j):return (j,0) if not i else (0,j)
    return fmpz_poly([int(d.get(k(j),0)) for j in range(F.degrees()[i]+1)])
def receipt(g):
    for p in primerange(2,800):
        f=nmod_poly(g.coeffs(),p)
        if f.degree()==g.degree() and not f.roots():return p

def normalize(F,bad):
    for i,G in enumerate(bad):
        c=0
        while 1:
            W=F.gcd(G)
            if all(d==0 for d in W.degrees()):break
            F,r=divmod(F,W)
            assert not r
            c+=1
        if c:print('removed',i,c,F.degrees(),flush=True)
    c=0
    for v in F.to_dict().values():c=gcd(c,int(v))
    return F//c

def pivot():
    raw=build(True)
    red=[]
    for f in raw:
        d=f.to_dict()
        A,r=divmod(f,u**min(e[0] for e in d)*z**min(e[1] for e in d))
        assert not r
        red.append(A)
    D,s,p=red
    a=univar(D.resultant(s,1),0).gcd(univar(D.resultant(p,1),0))
    c,fac=a.factor()
    assert a==c*prod(g**e for g,e in fac)
    assert sorted(g.degree() for g,e in fac)==[1,1,1,1,2,2,28]
    for g,e in fac:
        if g.degree()==1:
            r=Fraction(-int(g[0]),int(g[1]))
            assert r in (1,2,3,Fraction(1,2))
            print("forbidden pivot specialization",r)
        else:
            ell=receipt(g)
            assert ell
            print("pivot factor rootless",g.degree(),ell)

def cuts(terms):
    U=fmpz_poly([0,1])
    for u in (4,9):
        F=fmpz_poly([sum(v*u**i for (i,k),v in terms.items() if j==k) for j in range(19)])
        assert F.degree()==18 and receipt(F)==17
        print("fixed u, all rational z excluded",u)
    for label,Z,m in [("line through finite control",2*U-12,17),("extra reflected pair",U,19)]:
        F=sum(v*U**i*Z**j for (i,j),v in terms.items())
        assert F.degree()==38 and receipt(F)==m
        print(label,F.degree(),"projective rootless mod",m)

if __name__=='__main__':
    import argparse
    args=argparse.ArgumentParser()
    args.add_argument('--rebuild',action='store_true')
    b=args.parse_args()
    raw=json.loads(Path(__file__).with_name("affine-core.json").read_text())
    terms={tuple(e):int(v) for e,v in raw}
    assert len(terms)==399
    pivot()
    if b.rebuild:
        F,bad,*_=build()
        assert normalize(F,bad)==R.from_dict(terms)
    cuts(terms)
