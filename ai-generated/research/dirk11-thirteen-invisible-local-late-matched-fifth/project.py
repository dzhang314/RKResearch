from pathlib import Path
from runpy import run_path
from flint import nmod_poly
from fractions import Fraction
from itertools import permutations
import argparse
import sympy as S
q=run_path(str(Path(__file__).with_name('projection.py')))
K=q['K']; H=q['H']; T=q['T']; z=q['z']
def run(p):
 assert S.isprime(p) and p>11
 def rr(a):
  a=S.Rational(a)
  return int(a.p)*pow(int(a.q),-1,p)%p
 def nmp(a):
  if not isinstance(a,S.Poly):a=S.Poly(a,z,domain=S.QQ)
  return nmod_poly([rr(a.nth(i)) for i in range(a.degree()+1)] if not a.is_zero else [],p)
 nlc=rr(q['D156'].LC())
 assert nlc!=0
 modulus=nmp(K)
 assert modulus.degree()==156
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
 R0=E(nmod_poly([0,1],p))
 B=-pe(q['q0'])/pe(q['q1'])
 A=[pe(H.nth(i))/pe(H.LC()) for i in range(5)]
 assert ev(A,B)==0 and ev([pe(T.nth(i)) for i in range(4)],B)==0
 c2=A[3]+B;c1=A[2]+B*c2;c0=A[1]+B*c1
 a=[-9*c0,-(9*c0-6*c1)/2,-(c0-c1+3*c2)/2,E(1)]
 def plus(f,g):
  return [(f[i] if i<len(f) else E(0))+(g[i] if i<len(g) else E(0)) for i in range(max(len(f),len(g)))]
 def scale(f,n):return [x*n for x in f]
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
 U=[-36*c0,6*c1-12*c0,c1-c0,E(-1)]
 a0=plus(U,[0,0,0,-1]);b0=plus(scale(U,5),[0,0,0,-1])
 M=plus(plus(scale(mul(mul(a0,b0),[3*B,4*B-1]),2),scale(mul([3,2],mul(a0,a0)),-10*(B-1))),scale([E(0),*mul(U,b0)],-4*B))
 t=rem(M,a)
 T1=[t[2]*a[i]-(t[i-1] if i else 0) for i in range(3)]
 W=[t[2]*T1[i]-T1[2]*t[i] for i in range(2)]
 r=-W[0]/W[1]
 assert ev(a,r)==ev(M,r)==0
 s=r*r/(r+6); u=ev(U,r); de=r**3/(4*u); lam=E(Fraction(1,4))-de;l0=-de*c0/s;e=lam+l0
 (1+lam).inv();lam.inv();e.inv();r.inv();de.inv(); (B-1).inv(); B.inv()
 ps=[-r/(5*(2*r+3)),(4*r+3)/(5*(2*r+3))]
 xi=-r/(10*(2*r+3))
 fo=plus(scale(ps,1+lam),[lam,-lam])
 kn=plus(mul([l0,lam],fo),[0,-(1+lam)*xi,(1+lam)*xi])
 for name,x in [('fourth',E(1)),('fifth',B),('origin',1/R0)]:
  ev(kn,x).inv();print(f"F{p}: next {name} excludes e*K0=0",flush=True)
 old=[c0,c1,c2,E(1)]
 cols=[rem([E(0)]*j+kn+[E(0)],old) for j in range(3)]
 det=E(0)
 for a0 in permutations(range(3)):
  det+=(-1)**sum(a0[i]>a0[j] for i in range(3) for j in range(i+1,3))*cols[0][a0[0]]*cols[1][a0[1]]*cols[2][a0[2]]
 det.inv()
 print(f"F{p}: full old cubic norm excludes e*K0=0 at all three old roots",flush=True)

if __name__=='__main__':
 p=argparse.ArgumentParser()
 p.add_argument('--prime',type=int,action='append')
 a=p.parse_args()
 for prime in a.prime or [101]:
  run(prime)
