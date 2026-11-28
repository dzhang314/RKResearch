from pathlib import Path
from runpy import run_path
from flint import nmod_poly
from fractions import Fraction
from itertools import permutations
import argparse
import sympy as S
q=run_path(str(Path(__file__).with_name('projection.py')))
H=q['H']; T=q['T']; z=q['z']; ds=q['ds']
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

 class Old:
  def __init__(self,v):self.v=v
  @staticmethod
  def e(t):return t if isinstance(t,Old) else Old([E(t),E(0),E(0)])
  def __add__(self,t):return Old(plus(self.v,Old.e(t).v))
  __radd__=__add__
  def __neg__(self):return Old(scale(self.v,-1))
  def __sub__(self,t):return self+-Old.e(t)
  def __rsub__(self,t):return Old.e(t)+-self
  def __mul__(self,t):return Old(rem(mul(self.v,Old.e(t).v),a))
  __rmul__=__mul__
  def __pow__(self,n):
   y=Old.e(1)
   for _ in range(n):y*=self
   return y

 U=[-36*c0,6*c1-12*c0,c1-c0,E(-1)]
 rE=Old([E(0),E(1),E(0)])
 UE=Old(rem(U,a))
 t=q['fifth_gate'](rE,UE,Old.e(c0),Old.e(B)).v
 T1=[t[2]*a[i]-(t[i-1] if i else 0) for i in range(3)]
 W=[t[2]*T1[i]-T1[2]*t[i] for i in range(2)]
 r=-W[0]/W[1]
 assert ev(a,r)==0 and q['fifth_gate'](r,ev(U,r),c0,B)==0
 s=r*r/(r+6); u=ev(U,r); de=r**3/(4*u); lam=E(Fraction(1,4))-de;l0=-de*c0/s;e=lam+l0
 e.inv();r.inv();de.inv();(B-1).inv(); B.inv()
 ps=[-r/(5*(2*r+3)),(4*r+3)/(5*(2*r+3))]
 xi=-r/(10*(2*r+3)); Xi=[E(0),-xi,xi]
 ell=[l0,lam]
 rho=plus(mul(ps,ell),Xi)
 W0=scale(minus(scale(rho,1+lam),mul(ell,ell)),1/de)
 Delta=de/e
 K0=plus(ell,scale(W0,Delta))
 x=B
 assert x!=1 and x!=0
 d=ev(K0,x)
 assert d*(x-1+ev(ell,x))==(x-1)*ev(ell,x)
 d.inv(); (x-1).inv()
 qstar=(1-x)*Delta
 qstar.inv()
 L=plus(minus(mul([-x,E(1)],ell),rho),scale(W0,qstar))
 IP=B*B*(B*B/4+r*B/3+s/2)
 I2P=B**3*(B*B/20+r*B/12+s/6)
 IP0=B*B*(B**3/5+c2*B*B/4+c1*B/3+c0/2)
 for name,chk in [('fourth repeat',ev(L,E(1))),('consecutive weighted fifth twin',-I2P+qstar*IP0)]:
  chk.inv()
  print(f"degree {ds.degree()}, F{p}: next {name} gate is a full-field unit",flush=True)
 old=[c0,c1,c2,E(1)]
 cols=[rem([E(0)]*j+L+[E(0)],old) for j in range(3)]
 det=E(0)
 for a0 in permutations(range(3)):
  det+=(-1)**sum(a0[i]>a0[j] for i in range(3) for j in range(i+1,3))*cols[0][a0[0]]*cols[1][a0[1]]*cols[2][a0[2]]
 det.inv()
 print(f"degree {ds.degree()}, F{p}: norm excludes all three old repeats",flush=True)

if __name__=='__main__':
 p=argparse.ArgumentParser()
 p.add_argument('--prime',type=int,action='append')
 a=p.parse_args()
 for prime in a.prime or [101]:
  for rp in ds:
   run(prime,rp)
