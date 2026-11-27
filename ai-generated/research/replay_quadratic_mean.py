#!/usr/bin/env python3
"""Exact rational and mod-37 replay for the quadratic-mean ERK10 exclusion.

Only Python's standard library and the system GMP C++ compiler headers/library
are used. The finite checks cover quotient algebras of all selected roots;
they are not numerical or prime-height samples.
"""
from ast import literal_eval
from fractions import Fraction
from itertools import combinations, permutations
from math import comb, isqrt
from pathlib import Path
import subprocess
import tempfile

PRIME = 37
F6 = [-59, 283, 109, 1767, -864, 31860, 32400]
LOEX = [[35,15,17,1], [33,8,29,1]]

class NotUnit(Exception):pass
class Zp:
 def __init__(self,p):self.p=p;self.zero=0;self.one=1
 def mk(self,x):return int(x)%self.p
 def add(self,x,y):return (x+y)%self.p
 def neg(self,x):return -x%self.p
 def mul(self,x,y):return x*y%self.p
 def inv(self,x):
  if not x:raise NotUnit
  return pow(x,-1,self.p)
 def sub(self,x,y):return self.add(x,self.neg(y))
class Fq:
 def __init__(self,P,f):
  self.P=P;self.f=tuple(P.mk(c) for c in f);self.d=len(f)-1
  self.p=P.p;self.zero=self.mk(0);self.one=self.mk(1)
  self.x=self.mk(-f[0]) if self.d==1 else (0,1)+(0,)*(self.d-2)
 def mk(self,x):return (self.P.mk(x),)+(0,)*(self.d-1)
 def add(self,x,y):return tuple((a+b)%self.p for a,b in zip(x,y))
 def neg(self,x):return tuple(-a%self.p for a in x)
 def sub(self,x,y):return self.add(x,self.neg(y))
 def mul(self,x,y):
  z=[0]*(2*self.d-1)
  for i,xi in enumerate(x):
   if xi:
    for j,yj in enumerate(y):z[i+j]=(z[i+j]+xi*yj)%self.p
  for k in range(2*self.d-2,self.d-1,-1):
   if z[k]:
    for j in range(self.d):z[k-self.d+j]=(z[k-self.d+j]-z[k]*self.f[j])%self.p
  return tuple(z[:self.d])
 def inv(self,x):
  if x==self.zero:raise NotUnit
  return powr(self,x,self.p**self.d-2)
class Quad:
 def __init__(self,F,l,c):
  self.F=F;self.l=l;self.c=c;self.zero=(F.zero,F.zero);self.one=(F.one,F.zero);self.x=(F.zero,F.one)
 def mk(self,x):return (self.F.mk(x),self.F.zero)
 def embed(self,x):return (x,self.F.zero)
 def add(self,w,z):return self.F.add(w[0],z[0]),self.F.add(w[1],z[1])
 def neg(self,w):return self.F.neg(w[0]),self.F.neg(w[1])
 def sub(self,w,z):return self.add(w,self.neg(z))
 def mul(self,w,z):
  F=self.F;a,b=w;c,d=z;e=F.mul(b,d)
  return F.sub(F.mul(a,c),F.mul(self.c,e)),F.sub(F.add(F.mul(a,d),F.mul(b,c)),F.mul(self.l,e))
 def inv(self,x):
  F=self.F;a,b=x
  q=(F.sub(a,F.mul(b,self.l)),F.neg(b))
  nn=self.mul(x,q)
  assert nn[1]==F.zero
  cc=F.inv(nn[0]);return F.mul(q[0],cc),F.mul(q[1],cc)
def powr(F,x,n):
 y=F.one
 while n:
  if n&1:y=F.mul(x,y)
  x=F.mul(x,x);n//=2
 return y
def muls(F,*xs):
 o=F.one
 for c in xs:o=F.mul(o,c)
 return o
def adds(F,xs):
 o=F.zero
 for c in xs:o=F.add(o,c)
 return o
def div(F,x,y):return F.mul(x,F.inv(y))
def scale(F,x,n):return F.mul(F.mk(n),x)
def rat(F,a,b):return div(F,F.mk(a),F.mk(b))
def peval(F,c,x):
 y=F.zero
 for a in reversed(c):y=F.add(F.mul(y,x),a)
 return y
def mul(F,x,y):
 z=[F.zero]*(len(x)+len(y)-1)
 for i,a in enumerate(x):
  for j,b in enumerate(y):z[i+j]=F.add(z[i+j],F.mul(a,b))
 return z
def pad(F,x,n):return x+[F.zero]*(n-len(x))
def polsub(F,x,y):return [F.sub(a,b) for a,b in zip(pad(F,x,max(len(x),len(y))),pad(F,y,max(len(x),len(y))))]
def trim(F,x):
 while x and x[-1]==F.zero:x=x[:-1]
 return x
def rem(F,a,b):
 a=trim(F,a[:]);b=trim(F,b[:]);ib=F.inv(b[-1])
 while len(a)>=len(b):
  t=F.mul(a[-1],ib);j=len(a)-len(b)
  for i,c in enumerate(b):a[i+j]=F.sub(a[i+j],F.mul(c,t))
  a=trim(F,a)
 return a
def gcd(F,a,b):
 a=trim(F,a);b=trim(F,b)
 while b:a,b=b,rem(F,a,b)
 if not a:return []
 s=F.inv(a[-1]);return [F.mul(x,s) for x in a]
def quotroot(F,a,t):
 aa=a[:];rr=[F.zero]*(len(a)-1)
 for i in range(len(a)-1,0,-1):rr[i-1]=aa[i];aa[i-1]=F.add(aa[i-1],F.mul(t,aa[i]))
 assert aa[0]==F.zero
 return rr
def determinant(F,A):
 n=len(A);o=F.zero
 for p in permutations(range(n)):
  x=muls(F,*[A[i][p[i]] for i in range(n)])
  if sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))%2:x=F.neg(x)
  o=F.add(o,x)
 return o
def solve3(F,A,b):
 inv=F.inv(determinant(F,A))
 return [F.mul(inv,determinant(F,[[b[i] if k==j else A[i][k] for k in range(3)] for i in range(3)])) for j in range(3)]
def hull(F,roots):
 out=[F.one]
 for x in roots:out=mul(F,out,[F.neg(x),F.one])
 return out
def inte(F,q):return adds(F,[div(F,x,F.mk(i+1)) for i,x in enumerate(q)])
def prep(F,R,p):
 t=div(F,p,F.mk(2))
 val=div(F,peval(F,R,t),powr(F,t,3))
 out=R[:];out[2]=F.sub(out[2],F.mul(val,p));out[3]=F.add(out[3],val)
 q=quotroot(F,out,t)
 inv=F.inv(q[-1])
 return [F.mul(inv,x) for x in q[:2]]
def reflected(F,a):
 return [adds(F,[scale(F,a[j],comb(j,i)*(-1)**i) for j in range(i,len(a))]) for i in range(len(a))]

class Alg:
    """Monic polynomial quotient over an arbitrary finite coefficient ring."""
    def __init__(self,F,mod):
        self.F=F
        self.mod=tuple(mod)
        self.d=len(mod)
        self.zero=(F.zero,)*self.d
        self.one=(F.one,)+(F.zero,)*(self.d-1)
        self.x=(F.zero,F.one)+(F.zero,)*(self.d-2) if self.d>1 else (F.neg(mod[0]),)
    def mk(self,a):
        return self.embed(self.F.mk(a))
    def embed(self,a):
        return (a,)+(self.F.zero,)*(self.d-1)
    def add(self,a,b):
        return tuple(self.F.add(x,y) for x,y in zip(a,b))
    def sub(self,a,b):
        return tuple(self.F.sub(x,y) for x,y in zip(a,b))
    def neg(self,a):
        return tuple(self.F.neg(x) for x in a)
    def mul(self,a,b):
        F=self.F;d=self.d;c=[F.zero]*(d*2-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b):
                c[i+j]=F.add(c[i+j],F.mul(x,y))
        for i in range(2*d-2,d-1,-1):
            for j,z in enumerate(self.mod):
                c[i-d+j]=F.sub(c[i-d+j],F.mul(z,c[i]))
        return tuple(c[:d])
    def inv(self,a):
        F=self.F;v=a;rows=[]
        for _ in range(self.d):
            rows.append(v)
            v=self.mul(v,self.x)
        M=list(map(list,zip(*rows)))
        dd=F.inv(determinant(F,M))
        out=tuple(F.mul(dd,determinant(F,[[self.one[i] if k==j else M[i][k] for k in range(self.d)] for i in range(self.d)]))
                  for j in range(self.d))
        assert self.mul(a,out)==self.one
        return out

def split(prime, coefficients, expected):
    assert all(prime % d for d in range(2,isqrt(prime)+1))
    assert coefficients[-1] % prime
    actual=[x for x in range(prime) if sum(a*x**i for i,a in enumerate(coefficients))%prime==0]
    assert actual==expected and len(actual)==len(coefficients)-1
    return actual

def local_tower(F,R,p,q):
    """Universal algebras of both roots of the two chronological contacts."""
    t=div(F,p,F.mk(2))
    tau=div(F,F.add(F.one,q),F.mk(2))
    l,c=prep(F,R,p)
    k,d=prep(F,reflected(F,R),F.sub(F.one,q))
    X=Quad(F,l,c)
    W=Quad(X,X.embed(k),X.embed(d))
    lift=lambda a:W.embed(X.embed(a))
    x=W.embed(X.x)
    w=W.sub(W.one,W.x)
    P,Q,T,U=map(lift,[p,q,t,tau])
    return W,lift,[P,Q,T,U,x,w]

def models(F,R,p,q,t,tau,x,w,y,z):
    HL=hull(F,[t,x,y])
    HR=hull(F,[tau,w,z])
    PL=mul(F,[F.neg(p),F.one],polsub(F,[F.mul(R[0],a) for a in HL],
          [F.mul(HL[0],a) for a in R]))
    PR=mul(F,[F.neg(q),F.one],polsub(F,[F.mul(peval(F,R,F.one),a) for a in HR],
          [F.mul(peval(F,HR,F.one),a) for a in R]))
    return PL,PR
def J(F,a):return [F.zero]+[div(F,v,F.mk(i+1)) for i,v in enumerate(a)]
def form(F,a,b):return inte(F,mul(F,a,b))
def unit(F,a):
    """Check and multiply by the computed inverse, also in split quadratic rings."""
    ai=F.inv(a)
    assert F.mul(a,ai)==F.one

def linear_mean():
    P=37
    J3=[-1,9,-21,14]
    F=Zp(P)
    roots=split(P,J3,[12,19,26])
    count=0
    for p,q,a in permutations(roots):
        R=[F.neg(a),F.one,F.zero,F.zero]
        W,lift,[p,q,t,tau,x,w]=local_tower(F,R,p,q)
        R=list(map(lift,R))
        zero,one=W.zero,W.one
        BL=J(W,J(W,hull(W,[zero,t,p])))
        BR=reflected(W,J(W,J(W,hull(W,[zero,W.sub(one,tau),W.sub(one,q)]))))
        PL0,PR0=models(W,R,p,q,t,tau,x,w,zero,zero)
        PL1,PR1=models(W,R,p,q,t,tau,x,w,one,one)
        y0,y1=form(W,BR,PL0),form(W,BR,PL1)
        z0,z1=form(W,BL,PR0),form(W,BL,PR1)
        y=div(W,W.neg(y0),W.sub(y1,y0))
        z=div(W,W.neg(z0),W.sub(z1,z0))
        PL,PR=models(W,R,p,q,t,tau,x,w,y,z)
        unit(W,form(W,J(W,PL),PR))
        count+=1
    assert count==6
    return roots,count


def affine_reconstruct(W, R, p, q, t, tau, x, w):
    """Solve the two genuine affine seams after the local contacts."""
    zero,one=W.zero,W.one
    BL=J(W,J(W,hull(W,[zero,t,p])))
    BR=reflected(W,J(W,J(W,hull(W,[zero,W.sub(one,tau),W.sub(one,q)]))))
    PL0,PR0=models(W,R,p,q,t,tau,x,w,zero,zero)
    PL1,PR1=models(W,R,p,q,t,tau,x,w,one,one)
    y0,y1=form(W,BR,PL0),form(W,BR,PL1)
    z0,z1=form(W,BL,PR0),form(W,BL,PR1)
    y=div(W,W.neg(y0),W.sub(y1,y0))
    z=div(W,W.neg(z0),W.sub(z1,z0))
    return y,z

def jacobi_zero():
    F=Zp(PRIME)
    roots=split(PRIME,[1,-14,56,-84,42],[6,8,30,32])
    k=0
    for p,q in permutations(roots,2):
        a,b=[x for x in roots if x not in [p,q]]
        R=[F.mul(a,b),F.neg(F.add(a,b)),F.one,F.zero]
        W,lift,data=local_tower(F,R,p,q)
        R=list(map(lift,R))
        y,z=affine_reconstruct(W,R,*data)
        PL,PR=models(W,R,*data,y,z)
        unit(W,form(W,J(W,PL),PR))
        k+=1
    assert k==12
    return k

def infinity_repeat():
    F=Zp(PRIME)
    roots=split(PRIME,[-1,9,-21,14],[12,19,26])
    for q in roots:
        a,b=[x for x in roots if x!=q]
        R=[F.mul(a,b),F.neg(F.add(a,b)),F.one,F.zero]
        tau=div(F,F.add(F.one,q),F.mk(2))
        # The scaled outer X contact reduces to X²-r1·X-r0.
        X=Quad(F,F.neg(R[1]),F.neg(R[0]))
        ll,cc=prep(F,reflected(F,R),F.sub(F.one,q))
        W=Quad(X,X.embed(ll),X.embed(cc))
        lift=lambda a:W.embed(X.embed(a))
        x=W.embed(X.x)
        w=W.sub(W.one,W.x)
        Q,T=map(lift,[q,tau])
        R=list(map(lift,R))
        zero,one=W.zero,W.one
        BR=reflected(W,J(W,J(W,hull(W,[zero,W.sub(one,T),W.sub(one,Q)]))))
        def PL(y):
            a=hull(W,[x,y])
            # Removing the harmless scalar 1/2 from the scaled left model.
            return polsub(W,[W.mul(R[0],v) for v in a],
                          [W.mul(a[0],v) for v in R])
        def PR(z):
            b=hull(W,[T,w,z])
            return mul(W,[W.neg(Q),one],
                       polsub(W,[W.mul(peval(W,R,one),v) for v in b],
                              [W.mul(peval(W,b,one),v) for v in R]))
        BL=[zero,zero,zero,one]   # Removing the harmless scalar 1/12.
        y0,y1=form(W,BR,PL(zero)),form(W,BR,PL(one))
        z0,z1=form(W,BL,PR(zero)),form(W,BL,PR(one))
        y=div(W,W.neg(y0),W.sub(y1,y0))
        z=div(W,W.neg(z0),W.sub(z1,z0))
        unit(W,form(W,J(W,PL(y)),PR(z)))
    return roots

def exceptional_contacts():
    F=Zp(PRIME)
    factor_product=mul(F,LOEX[0],LOEX[1])
    assert [F.mk(x) for x in F6]==[F.mul(F.mk(F6[-1]),v) for v in factor_product]
    for pars in LOEX:
        assert all(peval(F,pars,x)!=0 for x in range(PRIME))  # A cubic with no root is irreducible.
        H=Fq(F,pars)
        dlt=H.x
        l0=[rat(H,x,42) for x in [1,-14,56,-84,42]]
        j0=[H.mul(dlt,rat(H,x,14)) for x in [-1,9,-21,14]]
        S=[H.add(x,y) for x,y in zip(l0,pad(H,j0,5))]
        derivative=[scale(H,c,i) for i,c in enumerate(S[1:],1)]
        assert gcd(H,S,derivative)==[H.one]
        common=gcd(H,S,[H.mul(c,rat(H,1,2**i)) for i,c in enumerate(S)])
        assert len(common)==2 and common[-1]==H.one
        p0=H.neg(common[0])
        assert p0!=H.zero
        P3=quotroot(H,S,p0)
        P=Alg(H,P3[:3])
        p=P.x
        Q3=quotroot(P,[P.embed(c) for c in S],p)
        K=Alg(P,Q3[:3])
        q=K.x
        p=K.embed(p)
        R=quotroot(K,[K.embed(x) for x in Q3],q)
        R.append(K.zero)
        W,lift,coords=local_tower(K,R,p,q)
        R=list(map(lift,R))
        y,z=affine_reconstruct(W,R,*coords)
        PL,PR=models(W,R,*coords,y,z)
        unit(W,form(W,J(W,PL),PR))
    return LOEX

def qmul(a,b):
    c=[Fraction(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            c[i+j]+=x*y
    return c

def qpow(a,n):
    out=[Fraction(1)]
    for _ in range(n):
        out=qmul(out,a)
    return out

def exact_quotient(a,b):
    a=list(a)
    q=[Fraction(0)]*(len(a)-len(b)+1)
    for j in range(len(q)-1,-1,-1):
        q[j]=a[j+len(b)-1]/b[-1]
        for i,v in enumerate(b):
            a[i+j]-=q[j]*v
    assert not any(a)
    return q

def rational_norms():
    src=Path(__file__).with_name('quadratic_mean_norms.cpp')
    with tempfile.TemporaryDirectory(prefix='erk-quadratic-mean-') as td:
        exe=Path(td)/'norm'
        subprocess.run(['g++','-O3','-std=c++17',str(src),'-lgmpxx','-lgmp',
                        '-o',str(exe)],check=True)
        result=subprocess.check_output([str(exe)],text=True).splitlines()
    assert len(result)==4
    assert result[0]=='0 336' and result[2]=='-1 336'
    f=[Fraction(x) for x in F6]
    mirror=[(-1)**i*x for i,x in enumerate(f)]
    exceptional=qmul(qmul(qpow([-1,3],36),qpow([1,3],36)),
                     qmul(qpow(f,8),qpow(mirror,8)))
    assert len(exceptional)==169
    F=Zp(PRIME)
    def integral_reduce(x):
        assert x.denominator%PRIME!=0
        return F.mul(F.mk(x.numerator),F.inv(F.mk(x.denominator)))
    assert integral_reduce(exceptional[-1])!=0
    quotients=[]
    for line in result[1::2]:
        norm=[Fraction(x) for x in literal_eval(line)]
        assert len(norm)==337 and norm[-1]!=0
        assert all(x.denominator%PRIME for x in norm)
        q=exact_quotient(norm,exceptional)
        mod=[integral_reduce(x) for x in q]
        assert len(mod)==169 and mod[-1]!=0
        quotients.append(mod)
    assert gcd(F,*quotients)==[F.one]
    return [336,336],[168,168]

if __name__=='__main__':
    print('zero-parameter Lobatto assignments:',jacobi_zero(),flush=True)
    print('infinite-parameter linear reductions:',linear_mean(),flush=True)
    print('infinite-parameter repeated-root choices:',infinity_repeat(),flush=True)
    print('exceptional finite contact factors:',exceptional_contacts(),flush=True)
    print('rational norm degrees, coprime reduced quotient degrees:',rational_norms(),flush=True)
