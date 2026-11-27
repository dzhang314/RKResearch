#!/usr/bin/env python3
"""Exact, dependency-free finite algebra replay for the ERK10 distinct-dormant seam."""
from itertools import combinations, permutations
from math import comb
from math import isqrt

PRIME = 41
E = [[11, -3, -196, 60, 882, -378, -1764, 1260, 1323, -1323], [10, 156, 630, -2184, -714, 5964, -2646], [-336, 210, 2184, -6636, 0, 7938], [294, -588, 2646, -10584], [-1323, 3969]]
O = [[-67, -126, 378, 1218, -1596, -3738, 4998, 2646, -3969], [222, -42, -924, 2940, -714, -7938, 10584], [168, 798, -4494, 7938, -7938], [210, -2646], [1323]]
J4 = [1, 0, -14, 0, 21]
G4 = [1, 0, -21, 0, 63]
S5 = [-11, 3, 42, -18, -63, 63]
G14 = [-2748, 8696, 79836, -432414, -1245339, 9348750, 15272853, -133142562, -16381260, 1084875624, -1844793216, -516287520, 4494130452, -4778612496, 1712893392]

M0 = [[17,12,1],[17,29,1],[20,2,28,29,40,1]]
M2 = [[6,1],[35,1],[35,1],[22,0,1],[38,32,5,33,11,31,5,7,17,5,16,5,17,1]]
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
def hpoly(F,coefs,hh):
 return [peval(F,[F.mk(a) for a in row],hh) for row in coefs]
def reflected(F,a):
 return [adds(F,[scale(F,a[j],comb(j,i)*(-1)**i) for j in range(i,len(a))]) for i in range(len(a))]

def main():
 P=PRIME
 check_factors()
 trace=dict(m0=0,m2=0, discarded=0, branch=0,seam=0)
 def candidate(F,hh,mm,d):
  N=F.neg;A=F.add;B=F.sub;M=F.mul
  p=div(F,A(F.one,A(mm,hh)),F.mk(2));q=div(F,A(F.one,B(mm,hh)),F.mk(2))
  tau=div(F,A(F.one,q),F.mk(2));t=div(F,p,F.mk(2))
  Q0=B(M(mm,mm),M(hh,hh));Q1=scale(F,mm,-2)
  def mom(k):
   def f(i):return F.zero if i%2 else rat(F,4,(i+1)*(i+3))
   return adds(F,[f(k+2),M(Q1,f(k+1)),M(Q0,f(k))])
  C=[[mom(i+j) for j in range(4)] for i in range(3)]
  for l,v in [(A(mm,hh),-1),(B(mm,hh),1)]:
   row=[scale(F,A(powr(F,l,j),scale(F,powr(F,div(F,A(l,F.mk(v)),F.mk(2)),j),4)),8) for j in range(4)]
   C.append(row)
  for I in combinations(range(5),4):
   D=determinant(F,[C[i] for i in I])
   try:F.inv(D);trace['discarded']+=1;return
   except NotUnit:pass
  trace['branch']+=1
  for M3 in combinations(range(5),3):
   try:r=solve3(F,[C[i][:3] for i in M3],[N(C[i][3]) for i in M3]);break
   except NotUnit:continue
  else:raise NotUnit('R rank')
  r=r+[F.one]
  # Monic X coordinates: substitute centered coordinate 2X−1.
  R=[div(F,adds(F,[scale(F,r[j],comb(j,i)*(2**i)*(-1)**(j-i)) for j in range(i,4)]),F.mk(8)) for i in range(4)]
  for j,v in enumerate([p,B(p,F.one),q,B(q,F.one),B(p,q),peval(F,R,F.zero),peval(F,R,F.one)]):
   try:F.inv(v)
   except NotUnit:raise NotUnit(f'base nonzero {j}')
  # Build virtual-residue congruence; no extraction of the three R roots.
  G=hull(F,[F.zero,F.one,p,q])
  I=[inte(F,[F.zero]*i+G) for i in range(3)]
  JR=[adds(F,[M(R[1],I[0]),M(R[2],I[1]),I[2]]),A(M(R[2],I[0]),I[1]),I[0]]
  # Lift into the universal algebra for the two local quadratic roots.
  try:
   l,c=prep(F,R,p)
   k,d=prep(F,reflected(F,R),B(F.one,q))
  except NotUnit:raise NotUnit('prep leading')
  X=Quad(F,l,c);W=Quad(X,X.embed(k),X.embed(d))
  lift=lambda a:W.embed(X.embed(a))
  zero,one=W.zero,W.one
  x=W.embed(X.x);w=W.sub(one,W.x)
  p,q,t,tau=map(lift,[p,q,t,tau])
  R,G,JR=([lift(v) for v in a] for a in [R,G,JR])
  D6=hull(W,[t,p,x,w,q,tau])
  gamma=rem(W,mul(W,JR,D6),R)
  cc=[pad(W,rem(W,[zero]*i+gamma,R),3) for i in range(3)]
  g=pad(W,rem(W,G,R),3)
  try:l,c,ka=solve3(W,[[cc[1][i],cc[0][i],g[i]] for i in range(3)],[W.neg(v) for v in cc[2]])
  except NotUnit:raise NotUnit('D reconstruction')
  Y=Quad(W,l,c);lift=Y.embed
  y=Y.x;z=Y.neg(Y.add(lift(l),y))
  p,q,t,tau,x,w=map(lift,[p,q,t,tau,x,w]);R=list(map(lift,R))
  HL=hull(Y,[t,x,y]);HR=hull(Y,[tau,w,z])
  PL=mul(Y,[Y.neg(p),Y.one],polsub(Y,[Y.mul(R[0],a) for a in HL],[Y.mul(HL[0],v) for v in R]))
  PR=mul(Y,[Y.neg(q),Y.one],polsub(Y,[Y.mul(peval(Y,R,Y.one),a) for a in HR],[Y.mul(peval(Y,HR,Y.one),v) for v in R]))
  form=inte(Y,mul(Y,[Y.zero]+[div(Y,v,Y.mk(i+1)) for i,v in enumerate(PL)],PR))
  try:Y.inv(form)
  except NotUnit:raise NotUnit('seam')
  trace['seam']+=1

 for d, factors in [(0,M0),(2,M2)]:
  for cc in map(list,dict.fromkeys(map(tuple,factors))):
   H=Fq(Zp(P),cc);hh=H.x
   trace["m"+str(d)]+=1
   if d==0:candidate(H,hh,H.zero,H.d)
   else:
    G=gcd(H,hpoly(H,E,hh),hpoly(H,O,hh))
    if len(G)==1:continue
    if len(G)!=2:raise NotUnit(f"base tau degree {len(G)-1}")
    tt=H.neg(G[0]);K=Quad(H,H.zero,H.neg(tt))
    candidate(K,K.embed(hh),K.x,H.d)
 if trace != {"m0":3,"m2":4,"discarded":4,"branch":3,"seam":3}:
  raise ValueError(trace)
 return trace

def check_factors():
 P=PRIME;F=Zp(P)
 assert all(P%d for d in range(2,isqrt(P)+1))
 for factors,left,right,scale0 in [(M0,J4,S5,11),(M2,G4,G14,17)]:
  product=[scale0]
  for f in factors:
   product=mul(F,product,f)
   n=len(f)-1
   def pow_mod(a,k):
    z=[1]
    while k:
     if k&1:z=rem(F,mul(F,z,a),f)
     a=rem(F,mul(F,a,a),f);k//=2
    return z
   X=rem(F,[0,1],f)
   assert pow_mod(X,P**n)==X
   for j in range(2,n+1):
    if n%j==0 and all(j%d for d in range(2,isqrt(j)+1)):
     assert gcd(F,polsub(F,pow_mod(X,P**(n//j)),X),f)==[1]
  assert product==mul(F,[v%P for v in left],[v%P for v in right])

if __name__=='__main__':
 print(PRIME, main())
