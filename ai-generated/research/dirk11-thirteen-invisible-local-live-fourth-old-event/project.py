from pathlib import Path
from runpy import run_path
from flint import nmod_poly
from fractions import Fraction
from itertools import permutations
import argparse
import sympy as S
q=run_path(str(Path(__file__).with_name('projection.py')))
H=q['H']; T=q['T']; z=q['z']; ds=[q['K']]
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
 Z=E(nmod_poly([0,1],p))
 B=-pe(q['q0'].rem(K))/pe(q['q1'].rem(K))
 A=[pe(H.nth(i))/pe(H.LC()) for i in range(5)]
 assert ev(A,B)==0 and ev([pe(T.nth(i)) for i in range(4)],B)==0
 c2=A[3]+B;c1=A[2]+B*c2;c0=A[1]+B*c1
 a=[-9*c0,-(9*c0-6*c1)/2,-(c0-c1+3*c2)/2,E(1)]
 def plus(f,g):
  return [(f[i] if i<len(f) else E(0))+(g[i] if i<len(g) else E(0)) for i in range(max(len(f),len(g)))]
 def scale(f,n):return [x*n for x in f]
 def minus(f,g):return plus(f,scale(g,-1))
 def mul(f,g):
  h=[E(0)]*(len(f)+len(g)-1)
  for i,x in enumerate(f):
   for j,y in enumerate(g):h[i+j]+=x*y
  return h
 def rem(f,g):
  assert g[-1]==1 and len(f)>=len(g)
  c=list(f)
  k=len(g)-1
  for i in range(len(c)-1,k-1,-1):
   for j in range(k):c[i-k+j]-=c[i]*g[j]
  return c[:k]

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

 def ratlin(t,a):
  U=[t[2]*a[i]-(t[i-1] if i else 0) for i in range(3)]
  W=[t[2]*U[i]-U[2]*t[i] for i in range(2)]
  return -W[0]/W[1]
 Old=Ext(a[:-1],E); rE=Old.gen()
 C=Ext(list(map(Old.c,[c0,c1,c2])),Old.c);xC=C.gen()
 Zx=q['old_gate'](C.c(rE),xC)
 M=norm([(Zx*xC**j).v for j in range(3)])
 r=ratlin(M.v,a)
 assert ev(a,r)==0 and ev(M.v,r)==0
 old=[c0,c1,c2,E(1)]
 O=Ext(old[:-1],E);xO=O.gen()
 ZO=q['old_gate'](O.c(r),xO)
 x=ratlin(ZO.v,old)
 assert ev(old,x)==0 and q['old_gate'](r,x)==0
 print(f"F{p}: exact r and old-event x reconstruction ratios live",flush=True)
 s=r*r/(r+6)
 U=r*(r+6)*c1-r**3-(r+6)**2*c0
 de=r**3/(4*U); lam=E(Fraction(1,4))-de;l0=-de*c0/s;e=lam+l0
 Delta=de/e
 de.inv();r.inv();(B-1).inv();(x-1).inv();x.inv();(B-x).inv()
 ps=[-r/(5*(2*r+3)),(4*r+3)/(5*(2*r+3))]
 xi=-r/(10*(2*r+3)); Xi=[E(0),-xi,xi]
 ell=[l0,lam]
 rho=plus(mul(ps,ell),Xi)
 W0=scale(minus(scale(rho,1+lam),mul(ell,ell)),1/de)
 K0=plus(ell,scale(W0,Delta))
 d=ev(K0,x); d.inv()
 assert d*(x-1+ev(ell,x))==(x-1)*ev(ell,x)
 qstar=(1-x)*Delta
 L=plus(minus(mul([-x,E(1)],ell),rho),scale(W0,qstar))
 assert ev(L,x)==0
 ev(L,E(1)).inv()
 print(f"F{p}: next fourth repeat unit",flush=True)
 oth=[c1+x*(c2+x),c2+x,E(1)]
 assert -x*oth[0]==c0
 norm([rem([E(0)]*i+L,oth) for i in range(2)]).inv()
 print(f"F{p}: both remaining old repeat roots unit",flush=True)
 ev(L,B).inv();ev(L,1/Z).inv()
 print(f"F{p}: next silent at fifth/origin after old marked completion units",flush=True)
 # Consecutive marked fifth: matched read, and separately zero-diagonal quintic.
 P=[E(0),s,r,E(1)];P0=[E(0),*old]
 def prim(q):return [E(0)]+[a/(i+1) for i,a in enumerate(q)]
 IP=prim(P); I2P=prim(IP);IP0=prim(P0)
 QB=(B-x)*ev(P,B)+qstar*ev(P0,B)
 JQ=(B-x)*ev(IP,B)-ev(I2P,B)+qstar*ev(IP0,B)
 LB=ev(L,B)
 (QB*LB-(B-x)*JQ).inv()
 print(f"F{p}: consecutive fifth nonzero diagonal unit",flush=True)

 P5=mul([-1,E(1)],P0); I5=prim(P5)
 Hs=[E(0),E(1),-14*Z,56*Z**2,-84*Z**3,42*Z**4]
 theta=ev(I5,x)/ev(Hs,x)
 E5=minus(I5,scale(Hs,theta))
 mo=xO*xO+O.c(r)*xO+O.c(s)
 qval=O.c(0)
 for coeff in reversed(E5[1:]):qval=qval*xO+O.c(coeff)
 qold=(qval/mo).v
 kV=ev(IP,E(1))/e
 Q5B=ev(qold,B)+(ev(E5,E(1))/kV-ev(qold,E(1)))*ev(old,B)/ev(old,E(1))
 (ev(E5,B)*LB-Q5B*JQ).inv()
 print(f"F{p}: consecutive fifth zero diagonal unit",flush=True)

if __name__=='__main__':
 p=argparse.ArgumentParser()
 p.add_argument('--prime',type=int,action='append')
 a=p.parse_args()
 for prime in a.prime or [101]:
  for rp in ds:
   run(prime,rp)
