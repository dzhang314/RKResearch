#!/usr/bin/env python3
"""Exact finite-algebra replay for the one-endpoint and linear-mean ERK10 exits."""
from itertools import permutations
from math import comb, isqrt

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

def one_endpoint():
    P=227
    L=[1,-14,56,-84,42]
    F=Zp(P)
    roots=split(P,L,[24,51,177,204])
    for q in roots:
        p=1
        R=quotroot(F,[div(F,F.mk(k),F.mk(42)) for k in L],q)
        G=hull(F,[0,1,p,q])
        I=[inte(F,[0]*i+G) for i in range(3)]
        JR=[adds(F,[F.mul(R[1],I[0]),F.mul(R[2],I[1]),I[2]]),
            F.add(F.mul(R[2],I[0]),I[1]),I[0]]
        H=hull(F,[0,1])
        W,lift,[p,q,t,tau,x,w]=local_tower(F,R,p,q)
        R,H,JR=([lift(v) for v in a] for a in [R,H,JR])
        D4=hull(W,[t,x,w,tau])
        gamma=rem(W,mul(W,JR,D4),R)
        cc=[pad(W,rem(W,[W.zero]*i+gamma,R),3) for i in range(3)]
        hc=pad(W,rem(W,H,R),3)
        l,c,_=solve3(W,[[cc[1][i],cc[0][i],hc[i]] for i in range(3)],
                      [W.neg(v) for v in cc[2]])
        Y=Quad(W,l,c)
        y=Y.x
        z=Y.neg(Y.add(Y.embed(l),y))
        p,q,t,tau,x,w=map(Y.embed,[p,q,t,tau,x,w])
        PL,PR=models(Y,list(map(Y.embed,R)),p,q,t,tau,x,w,y,z)
        unit(Y,form(Y,J(Y,PL),PR))
    return roots

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

if __name__=='__main__':
    print('prime 227, endpoint-root seams:', one_endpoint())
    print('prime 37, linear-mean seams:', linear_mean())
