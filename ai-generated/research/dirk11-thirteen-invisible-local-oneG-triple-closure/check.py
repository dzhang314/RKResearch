from pathlib import Path
from runpy import run_path
from flint import nmod_poly
from fractions import Fraction
import argparse
import sympy as S
q=run_path(str(Path(__file__).with_name('projection.py')))
H=q['H']; z=q['z']
def run(p,ds):
 K=ds.monic()
 assert S.isprime(p) and p>11
 def rr(a):
  a=S.Rational(a)
  return int(a.p)*pow(int(a.q),-1,p)%p
 def nmp(a):
  if not isinstance(a,S.Poly):a=S.Poly(a,z,domain=S.QQ)
  return nmod_poly([rr(a.nth(i)) for i in range(a.degree()+1)] if not a.is_zero else [],p)

 assert rr(ds.LC())!=0
 modulus=nmp(K)
 assert modulus.degree()==ds.degree()
 class E:
  def __init__(self,a):
   if isinstance(a,E):self.q=a.q
   elif isinstance(a,nmod_poly):self.q=a%modulus
   else:
    a=Fraction(a); self.q=nmod_poly([a.numerator*pow(a.denominator,-1,p)%p],p)
  def __add__(self,b):return E(self.q+E(b).q)
  __radd__=__add__
  def __neg__(self):return E(-self.q)
  def __sub__(self,b):return self+-E(b)
  def __rsub__(self,b):return E(b)+-self
  def __mul__(self,b):return E(self.q*E(b).q)
  __rmul__=__mul__
  def inv(self):
   d,a,b=self.q.xgcd(modulus)
   assert d==1,"nonunit gcd degree %s"%d.degree()
   u=E(a)
   assert self*u==1
   return u
  def __truediv__(self,b):return self*E(b).inv()
  def __rtruediv__(self,b):return E(b)*self.inv()
  def __pow__(self,n):
   a=E(1); b=self
   while n:
    if n%2:a*=b
    b*=b;n//=2
   return a
  def __eq__(self,b):return self.q==E(b).q
 def pe(e):return E(nmp(e))
 def ev(c,y):
  a=E(0)
  for v in reversed(c):a=a*y+v
  return a
 def det(M):
  if len(M)==1:return M[0][0]
  return sum((-1)**j*e*det([[v for k,v in enumerate(row) if k!=j] for row in M[1:]])
             for j,e in enumerate(M[0]))
 def norm(cols):
  return det(list(zip(*cols)))
 def Ext(conf,base):
  n=len(conf)
  class Cls:
   def __init__(self,v):self.v=v
   @staticmethod
   def c(t):return t if isinstance(t,Cls) else Cls([base(t)]+[base(0)]*(n-1))
   @staticmethod
   def gen():return Cls([base(0),base(1)]+[base(0)]*(n-2))
   def __add__(self,t):return Cls([a+b for a,b in zip(self.v,Cls.c(t).v)])
   __radd__=__add__
   def __neg__(self):return Cls([-a for a in self.v])
   def __sub__(self,t):return self+-Cls.c(t)
   def __rsub__(self,t):return Cls.c(t)+-self
   def __mul__(self,t):
    arr=[base(0)]*(2*n-1)
    for i,a in enumerate(self.v):
     for j,b in enumerate(Cls.c(t).v): arr[i+j]+=a*b
    for i in range(2*n-2,n-1,-1):
     for j in range(n):arr[i-n+j]-=arr[i]*conf[j]
    return Cls(arr[:n])
   __rmul__=__mul__
   def __pow__(self,k):
    ans=Cls.c(1);b=self
    while k:
     if k%2:ans*=b
     b*=b;k//=2
    return ans
   def __eq__(self,b):return self.v==Cls.c(b).v
   def inv(self):
    M=list(zip(*[(self*Cls.gen()**j).v for j in range(n)]))
    cof=[(-1)**j*det([[v for k,v in enumerate(row) if k!=j] for row in M[1:]]) for j in range(n)]
    d=sum(a*b for a,b in zip(cof,M[0])).inv()
    z=Cls([c*d for c in cof]);assert self*z==1
    return z
   def __truediv__(self,b):return self*Cls.c(b).inv()
   def __rtruediv__(self,b):return Cls.c(b)*self.inv()
  return Cls

 Z=E(nmod_poly([0,1],p))
 r=-pe(q['n0'])/pe(q['n1'])
 assert r!=0
 def eval2(F):
  f=S.Poly(F,q['r'],domain=S.QQ[z])
  return ev([pe(f.nth(i)) for i in range(f.degree()+1)],r)
 assert eval2(q['p0'])==eval2(q['p1'])==0
 s=r*r/(r+6); r.inv(); (2*r+3).inv();s.inv()
 hh=[pe(H.nth(i))/pe(H.LC()) for i in range(5)]
 ca=hh[3]-r; cb=hh[2]-s-ca*r
 assert hh[1]==ca*s+cb*r and hh[0]==cb*s
 # All complement roots in one finite-free degree-two extension.
 Xb=Ext([cb,ca],E); b=Xb.gen(); a=-Xb.c(ca)-b
 P=lambda x:x*(x*x+x*r+s)
 IP=lambda x:x*x*(x*x/4+x*r/3+s/2)
 I2P=lambda x:x*x*x*(x*x/20+x*r/12+s/6)
 # Extend scalars explicitly when evaluating a polynomial over Xb.
 psi1=(4*r+3)/(5*(2*r+3)); psi0=-r/(5*(2*r+3)); xi=-r/(10*(2*r+3))
 (psi1+psi0).inv()
 def mnorm(u0,u1):
  return u0*u0-u0*u1*r+u1*u1*s
 mnorm(psi0+1,psi1-1).inv()
 pb=P(b); pa=P(a); pa.inv(); pb.inv()
 la=IP(a)/pa; ra=I2P(a)/pa
 t=b-1
 (t).inv(); (a-1).inv()
 (ra*(a-1+la)-(a-1)*la*la).inv()
 print(f"F{p}: all immediate repeats after fourth impossible (4 labels, both complement assignments)",flush=True)

 psi=b*psi1+psi0
 (psi-t).inv()
 print(f"F{p}: matched D0 on marked triple second return after fourth is impossible",flush=True)
 S2=Ext([-b*xi/t, (b*xi-psi)/t],Xb.c); y=S2.gen()
 # y=d_B/(b-1). Companion argument after fifth gives a linear gate at each
 # repeated old label and a primitive gate at the sole G label.
 u0=y+psi0; u1=-y+psi1
 mnorm(u0,u1).inv()
 (-(y*t*IP(b))+I2P(b)).inv()
 print(f"F{p}: third marked-triple member cannot be the same-clock next row (paid full-class primitive unit)",flush=True)
 (-y*(a-1)*la+ra).inv()
 print(f"F{p}: old marked returns and the unmarked G return impossible after fifth (full rank120)",flush=True)
if __name__=='__main__':
 p=argparse.ArgumentParser()
 p.add_argument('--prime',type=int,action='append')
 a=p.parse_args()
 for prime in a.prime or [103]:
   run(prime,q['D'])
