#!/usr/bin/env python3
"""Norms for the general exceptional diagonal fiber J3."""
from flint import fmpq_poly,fmpq
from math import gcd
q=fmpq_poly([0,1])
J=1225*q**8+9450*q**7+24640*q**6+25230*q**5+9639*q**4-480*q**3-1212*q*q-360*q-36
D=175*q**4+588*q**3+279*q*q+72*q+6
N=(35*q*q+30*q+3)*(35*q**4+140*q**3+131*q*q+40*q+6)
one,c,_=D.xgcd(J)
assert one==1 and (c*D)%J==1
K=(c*N/5)%J
paid=(2,3,5,7,59,6359)
def strip(u):
 if u==0:return 0
 for p in paid:
  while u%p==0:u//=p
 return u
def guard(f):
 for c in f.coeffs():assert strip(int(c.denominator))==1
guard(c);guard(K)
class F:
 def __init__(self,x=0,y=0):
  self.a=(fmpq_poly([x]) if isinstance(x,(int,fmpq)) else x)%J
  self.b=(fmpq_poly([y]) if isinstance(y,(int,fmpq)) else y)%J
 def __add__(self,x):
  if not isinstance(x,F):x=F(x)
  return F(self.a+x.a,self.b+x.b)
 __radd__=__add__
 def __neg__(self):return F(-self.a,-self.b)
 def __sub__(self,x):return self+-x
 def __rsub__(self,x):return x+-self
 def __mul__(self,x):
  if not isinstance(x,F):x=F(x)
  return F(self.a*x.a+K*self.b*x.b,self.a*x.b+self.b*x.a)
 __rmul__=__mul__
 def __bool__(self):return bool(self.a or self.b)
 def mirror(self):return F(self.a,-self.b)
 def norm(self):return (self.a*self.a-K*self.b*self.b)%J
class G:
 def __init__(self,x=0):
  if isinstance(x,G):self.v=x.v
  elif isinstance(x,(int,F)):self.v=[x if isinstance(x,F) else F(x)]
  else:self.v=list(x)
  while len(self.v)>1 and not self.v[-1]:self.v.pop()
 def __getitem__(self,i):return self.v[i] if i<len(self.v) else F()
 def __add__(self,x):
  x=G(x);return G([self[i]+x[i] for i in range(max(len(self.v),len(x.v)))])
 __radd__=__add__
 def __neg__(self):return G([-a for a in self.v])
 def __sub__(self,x):return self+-G(x)
 def __rsub__(self,x):return G(x)+-self
 def __mul__(self,x):
  x=G(x);v=[F()]*(len(self.v)+len(x.v)-1)
  for i,a in enumerate(self.v):
   if not a:continue
   for j,b in enumerate(x.v):
    if b:v[i+j]+=a*b
  return G(v)
 __rmul__=__mul__
 def __bool__(self):return any(self.v)
 def __pow__(self,n):
  if n==0:return G(1)
  v=self**(n//2);return v*v*(self if n%2 else G(1))
 def mirror(self):return G([c.mirror() for c in self.v])
def det(A,Z,O):
 n=len(A);states={0:O}
 for j,row in enumerate(A):
  nxt={}
  for key,t in states.items():
   if not t:continue
   for i,c in enumerate(row):
    if key&(1<<i) or not c:continue
    kk=key|(1<<i)
    v=t*c
    if (key>>(i+1)).bit_count()%2:v=-v
    nxt[kk]=nxt.get(kk,Z)+v
  states=nxt
 return states.get((1<<n)-1,Z)
def res(A,B,Z,O):
 m,n=len(A)-1,len(B)-1
 pad=lambda a,i:[Z]*i+a[::-1]+[Z]*(m+n-i-len(a))
 return det([pad(A,i) for i in range(n)]+[pad(B,i) for i in range(m)],Z,O)
k=F(0,1)
TR=F((-105*K*q-15*K+175*q**3+255*q*q+105*q+9)%J)
p0=k*F(3*(-21*K+35*q*q+42*q+15)/7)
p1=F(-3*(-175*K*q-21*K+245*q**3+385*q*q+171*q+15)/7)
p2=-3*k*F(-5*K+15*q*q+10*q+3)
p=[p0,p1,p2,TR]
g=G([F(),F(1)]);qq=G(F(q));kk=G(k)
h=[2-3*kk+6*qq-12*g*qq,6*qq-12*g*kk,3*kk-12*g,G(2)]
H=res([G(x) for x in p],h,G(0),G(1));HH=H.mirror()
assert len(H.v)==len(HH.v)==4
ans=[]
def norm(f):
 guard(f.a);guard(f.b)
 u=f.norm();guard(u)
 return abs(int(J.resultant(u).numerator))
A0=norm(res(H.v,HH.v,F(),F(1)))
print('both anchor support bitlength',strip(A0).bit_length(),strip(A0) if strip(A0).bit_length()<=200 else '',flush=True)
ans.append(A0)
r=(2*g-1)**2+kk*(2*g-1)+qq
d=r+4*g**2;u=2*r-2*g*(4*g-2+kk)
FF=-2*d**3+u*d*d+4*u*u*d-u**3-2*r*(3*u-2*d)*d
Q=4*u**3-12*u*u*d+3*u*d*d+2*d**3
z=2*g*(d+2*u)-d
pin=G(TR)*z**3+G(p2)*z*z*d+G(p1)*z*d*d+G(p0)*d**3
for tag,ps in [('A',[FF]),('Z',[Q,pin])]:
   ns=A0
   for F0 in ps:
      R=norm(res(H.v,F0.v,F(),F(1)))
      ns=gcd(R,ns)
      print('after',tag,len(F0.v)-1,'norm support gcd',strip(ns),'bits',strip(ns).bit_length(),flush=True)
   ans.append(ns)
assert [strip(v) for v in ans[1:]]==[11,1]
print('phase norm gcds', [strip(v) for v in ans[1:]])
