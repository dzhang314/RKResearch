#!/usr/bin/env python3
"""Exact finite arithmetic for the genus-two DIRK10 rational obstruction.

Section one implements the standard odd-degree x-theta 2-descent
arithmetic. Section two uses exact Cantor arithmetic over Q and F_11
and computes the two local Abel-Jacobi logarithms modulo 11^2.
No external dependencies and no heuristic rank or rational-point search.
"""
from fractions import Fraction as Q
from itertools import product
from functools import lru_cache

P2=lambda p,e:Q(p)**e
def ordp(x,p):
 x=Q(x);assert x
 a,b,n=abs(x.numerator),x.denominator,0
 while not a%p:a//=p;n+=1
 while not b%p:b//=p;n-=1
 return n
def mod(x,p):
 x=Q(x)
 return x.numerator*pow(x.denominator,-1,p)%p
def mul(a,b,u=-1,v=-5):  # eta^2=-u eta-v
 return (a[0]*b[0]-v*a[1]*b[1],a[0]*b[1]+a[1]*b[0]-u*a[1]*b[1])
def norm(x,u=-1,v=-5):
 a,b=x
 return a*a-u*a*b+v*b*b
def powq(a,n,u=-1,v=-5):
 if n<0:
  N=norm(a,u,v)
  a=((a[0]-u*a[1])/Q(N),-a[1]/Q(N));n=-n
 r=(1,0)
 while n:
  if n&1:r=mul(r,a,u,v)
  n//=2
  if n:a=mul(a,a,u,v)
 return r
def m8(a,b,u,v):return tuple(x%8 for x in mul(a,b,u,v))

@lru_cache(None)
def unit2table(u,v):
 units=[(a,b)for a,b in product(range(8),repeat=2)if a%2 or b%2]
 sq={m8(z,z,u,v)for z in units}
 assert len(sq)==6
 code={z:0 for z in sq};i=1
 for a in units:
  if a in code:continue
  code.update({m8(a,z,u,v):i|val for z,val in list(code.items())})
  i*=2
 assert i==8 and len(code)==48
 return code
def cl_unram(a,p,u,v):
 m=min(ordp(x,p)for x in a if x)
 A=tuple(x/P2(p,m)for x in a)
 if p==2:return (m%2)|2*unit2table(u,v)[tuple(mod(x,8)for x in A)]
 n=mod(norm(A,u,v),p)
 assert n
 return (m%2)|2*int(pow(n,(p-1)//2,p)!=1)
def cl_q(a,p):
 assert a
 if p==0:return int(a<0)
 m=ordp(a,p);A=a/P2(p,m)
 if p==2:return (m%2)|{1:0,3:6,5:4,7:2}[mod(A,8)]
 return (m%2)|2*int(pow(mod(A,p),(p-1)//2,p)!=1)
@lru_cache(None)
def lift5(n,i):
 m=1
 while m<n:
  m=min(2*m,n);q=5**m
  i=(i-(i*i-i-5)*pow(2*i-1,-1,q))%q
 return i
def signquad(a,b):
 a,b=a+b/2,b/2
 if not b:return int(a<0)
 if a*b>=0:return int(b<0)
 return int(b<0) if a*a<21*b*b else int(a<0)
def cl_k(a,p):
 if p==0:
  a,b=map(Q,a)
  return signquad(a,b)|2*signquad(a+b,-b)
 if p==2:return cl_unram(a,p,-1,-5)
 if p in (3,7):
  m=ordp(norm(a),p)
  u=mul(a,powq((-1,2),-m))
  z=(mod(u[0],p)+pow(2,-1,p)*mod(u[1],p))%p
  assert z
  return (m%2)|2*int(pow(z,(p-1)//2,p)!=1)
 assert p==5
 m=min(ordp(x,p)for x in a if x)
 a=tuple(x/P2(p,m)for x in a)
 s=ordp(norm(a),p)
 M=5**(s+1)
 pos=[(mod(a[0],M)+mod(a[1],M)*lift5(s+1,i))%M for i in (0,1)]
 assert all(pos)
 v0,v1=[cl_q(x,p)^(m%2) for x in pos]
 return v0|v1<<2
def full_cl(x,p):
 # field (Q,Q,Q,K) x coordinates converted to bit vector
 bits=1 if p==0 else 3 if p==2 else 2
 return cl_q(x[0],p)|(cl_q(x[1],p)<<bits)|(cl_q(x[2],p)<<(2*bits))|(cl_k(x[3],p)<<(3*bits))

def reduction(a,piv):
 for j,b in reversed(sorted(piv.items())):
  if (a>>j)&1:a^=b
 return a
def row_insert(a,piv):
 a=reduction(a,piv)
 if a:
  piv[a.bit_length()-1]=a
  return True
 return False
def poly_f(x):return x*(x*x-21)*(x*x-81)
def point_kum(x):
 u=[x,x-9,x+9]
 vs=[21*81,2*81*60,2*81*60]
 if not all(u):
  u=[v if v else vs[i] for i,v in enumerate(u)]
 return (*u,(x+1,-2))
LOCAL_POINTS = {0:(-9,0),2:(0,9,-9,1,20),3:(0,9,-9),
                5:(9,-9,1,24),7:(0,-9,1)}
LOCAL_CODES = {0:[27,10],2:[1044,6744,6874,2904,1332],
               3:[201,228,210],5:[612,408,952,748],
               7:[203,138,40]}

def local_img(p):
    # Each displayed rational x has an actual ordinate in the local field.
    # At an exact Weierstrass point the derivative evaluation is used.
    target={0:2,2:5,3:3,5:4,7:3}[p]
    piv = {}; codes = []
    for xx in LOCAL_POINTS[p]:
        x=Q(xx)
        fx=poly_f(x)
        assert not fx or cl_q(fx,p)==0
        mask=full_cl(point_kum(x),p)
        assert row_insert(mask,piv)
        codes.append(mask)
    assert codes==LOCAL_CODES[p] and len(piv)==target
    return piv

def globalbasis():
 B=[]
 for j in range(3):
  for x in (-1,2,3,5,7):
   a=[1,1,1];a[j]=x;B.append((*a,(1,0)))
 # epsilon=(5+sqrt21)/2=2+omega; rho3=(3+sqrt21)/2=1+omega
 for a in [(-1,0),(2,1),(2,0),(1,1),(3,1),(0,1),(1,-1)]:
  B.append((1,1,1,a))
 return B
def primesclass_q(a):
 n=int(a<0);u=abs(a)
 for i,p in enumerate((2,3,5,7),1):
  v0=ordp(u,p)
  n|=((v0%2)<<i);u/=P2(p,v0)
 assert u==1
 return n
def maskrows(cols):
 for j in range(max(c.bit_length() for c in cols)):
  yield sum((int(bool((c>>j)&1))<<i) for i,c in enumerate(cols))
def descent_receipts():
    basis=globalbasis(); assert len(basis)==22
    norm_cols=[primesclass_q(a*b*c*norm(d)) for a,b,c,d in basis]
    G={}
    for row in maskrows(norm_cols):
        row_insert(row,G)
    dims=[len(basis)-len(G)]
    local_data=[]
    for p in (0,2,3,5,7):
        L=local_img(p)
        columns=[full_cl(x,p) for x in basis]
        cols=[reduction(a,L)for a in columns]
        for row in maskrows(cols):
            row_insert(row,G)
        dims.append(len(basis)-len(G))
        local_data.append((LOCAL_CODES[p],columns))
    assert dims==[17,15,10,7,4,4]
    return norm_cols,local_data,dims


class PolyField:
 def __init__(self,p=0): self.p=p
 def cn(self,x):
  if not self.p:return Q(x)
  x=Q(x);return (x.numerator*pow(x.denominator,-1,self.p))%self.p
 def inv(self,x):return Q(1)/x if not self.p else pow(x,-1,self.p)
 def tr(self,a):
  a=[self.cn(x)for x in a]
  while a and not a[-1]:a.pop()
  return a
 def scl(self,a,c):return self.tr(x*c for x in a)
 def add(self,a,b):
  return self.tr((a[i]if i<len(a)else 0)+(b[i]if i<len(b)else 0)
                 for i in range(max(len(a),len(b))))
 def sub(self,a,b):return self.add(a,self.scl(b,-1))
 def mul(self,a,b):
  if not a or not b:return []
  t=[0]*(len(a)+len(b)-1)
  for i,x in enumerate(a):
   for j,y in enumerate(b):t[i+j]+=x*y
  return self.tr(t)
 def dv(self,A,b):
  A=self.tr(A);q=[0]*max(0,len(A)-len(b)+1);inv=self.inv(b[-1])
  while len(A)>=len(b):
   j=len(A)-len(b);c=self.cn(A[-1]*inv);q[j]=c
   A=self.sub(A,[0]*j+self.scl(b,c))
  return self.tr(q),A
 def exact(self,a,b):
  q,r=self.dv(a,b);assert not r
  return q
 def mod(self,a,b):return self.dv(a,b)[1]
 def monic(self,a):return self.scl(a,self.inv(a[-1]))
 def xgcd(self,a,b):
  u,v,x,y=[1],[],[],[1]
  while b:
   q,r=self.dv(a,b)
   a,b=b,r
   u,v=v,self.sub(u,self.mul(q,v))
   x,y=y,self.sub(x,self.mul(q,y))
  scale=self.inv(a[-1])
  return self.scl(a,scale),self.scl(u,scale),self.scl(x,scale)
 def ev(self,a,x):
  z=0
  for b in a[::-1]:z=self.cn(z*x+b)
  return z

class Jac:
 INF=([1],[])
 def __init__(self,p=0):
  self.K=PolyField(p);self.F=self.K.tr([0,1701,0,-102,0,1])
 def pt(self,x,y):
  K=self.K; u=K.tr([-x,1]);v=K.tr([y]);assert K.ev(self.F,x)==K.cn(y*y)
  return u,v
 def validate(self,D):
  u,v=D;K=self.K
  assert 1<=len(u)<=3 and u[-1]==1 and (not v or len(v)<len(u))
  assert not K.mod(K.sub(self.F,K.mul(v,v)),u)
 def add(self,D,E):
  u1,v1=D;u2,v2=E
  K=self.K
  d0,e1,e2=K.xgcd(u1,u2)
  d,a,b=K.xgcd(d0,K.add(v1,v2))
  e1,e2,e3=K.mul(a,e1),K.mul(a,e2),b
  u=K.exact(K.mul(u1,u2),K.mul(d,d))
  v=K.mod(K.exact(K.add(K.add(K.mul(K.mul(e1,u1),v2),K.mul(K.mul(e2,u2),v1)),
                        K.mul(e3,K.add(K.mul(v1,v2),self.F))),d),u)
  while len(u)>3:
   u=K.monic(K.exact(K.sub(self.F,K.mul(v,v)),u))
   v=K.mod(K.scl(v,-1),u)
  ans=(u,v);self.validate(ans)
  return ans
 def mul(self,n,D):
  E=self.INF
  while n:
   if n&1:E=self.add(E,D)
   n//=2
   if n:D=self.add(D,D)
  return E

def logarithm():
 p=11;Jp=Jac(p);J=Jac()
 P=J.pt(1,40);Pp=Jp.pt(1,40);Op=Jp.INF
 A=Op
 for n in range(1,300):
  A=Jp.add(A,Pp)
  if A==Op:break
 else:raise AssertionError
 assert n==28
 N=J.mul(n,P)
 assert N!=J.INF
 # Check the binary composition against sequential exact composition.
 M0=J.INF
 for _ in range(n):M0=J.add(M0,P)
 assert N==M0
 Q0=J.pt(9,0)
 B=J.add(P,Q0)
 D=J.add(N,B)
 mod=lambda x,m: int(x.numerator)*pow(int(x.denominator),-1,m)%m
 M=p*p
 dat=[[mod(x,M)for x in A]for A in D]
 assert dat==[[97,34,1],[67,72]]
 assert all(x.denominator%11 for u0 in D for x in u0)
 Kp=PolyField()
 u,v=dat
 H=[j for j in range(M) if Kp.ev(u,j)%M==0]
 coords=[(j,Kp.ev(v,j)%M)for j in H]
 assert coords==[(9,110),(78,117)]
 for x,y in coords:
  assert (y*y-poly_f(x))%M==0
 S=[0,0]
 for x,y in coords:
  if x%p==1:
   assert y%p==40%p
   C=((x-1)//p)*pow(2*40,-1,p)%p;r=1
  elif x%p==9:
   assert y%p==0
   C=(y//p)*pow(2*81*60,-1,p)%p;r=9
  else:raise AssertionError
  S[0]=(S[0]+C)%p;S[1]=(S[1]+r*C)%p
 assert S==[9,0]
 return S

if __name__=="__main__":
    _, _, dims=descent_receipts()
    assert 16*81**3*21**3*60**4==2**12*3**19*5**4*7**3
    print("2-descent remaining dimensions",dims)
    print("genus-two rank at most 4−3=1")
    S=logarithm()
    print("good prime 11: reduced order of D is 28; translated support mod 121:")
    print("  (9,110), (78,117); log(28D)/11 mod 11 =",S)
    print("exact 2-descent and two-disk logarithm arithmetic PASS")
