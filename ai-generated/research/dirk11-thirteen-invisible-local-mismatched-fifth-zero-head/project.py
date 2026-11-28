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

 def norm(cols):
  return sum((-1)**sum(j[i]>j[k] for i in range(3) for k in range(i+1,3))*cols[0][j[0]]*cols[1][j[1]]*cols[2][j[2]] for j in permutations(range(3)))
 mr=[108*B**4,72*B**4+288*B**3,15*B**4+144*B**3+288*B**2,
     B**4+16*B**3+108*B**2+120*B,10*B**2+20*B+20]
 t=rem(mr,a)
 U2=[t[2]*a[j]-(t[j-1] if j else 0) for j in range(3)]
 W1=[t[2]*U2[j]-U2[2]*t[j] for j in range(2)]
 rho=-W1[0]/W1[1]
 assert ev(a,rho)==0 and ev(mr,rho)==0
 old=[c0,c1,c2,E(1)]
 ss=rho*rho/(rho+6)
 Ur=rho*(rho+6)*c1-rho**3-(rho+6)**2*c0
 delta=rho**3/(4*Ur); lam=E(Fraction(1,4))-delta
 ell0=-delta*c0/ss; ell=[ell0,lam]; e=ev(ell,E(1)); Delta=delta/e
 psi=[-rho/(5*(2*rho+3)),(4*rho+3)/(5*(2*rho+3))]
 xi=-rho/(10*(2*rho+3)); xiP=[E(0),-xi,xi]
 Rho=plus(mul(psi,ell),xiP)
 # Khat=e K0; Lhat=e L. No 1+lambda division.
 Khat=minus(scale(Rho,1+lam),scale(mul([E(-1),E(1)],ell),lam))
 P_B=B*(B*B+rho*B+ss); P0_B=B*ev(old,B)
 f=-P_B-Delta*P0_B
 v=-(B-1)*P_B/f
 Lhat=minus(scale(minus(mul([E(-1),E(1)],ell),Rho),e),scale(Khat,v))
 for name,x in [('fourth',E(1)),('origin',1/Z)]:
  ev(Lhat,x).inv()
  print(f"F{p}: zero fifth, next {name} impossible (unit eL)",flush=True)
 cols=[rem([E(0)]*j+Lhat+[E(0)],old) for j in range(3)]
 norm(cols).inv()
 print(f"F{p}: zero fifth, any of 3 old next events impossible (unit old cubic norm of eL)",flush=True)
if __name__=='__main__':
 p=argparse.ArgumentParser()
 p.add_argument('--prime',type=int,action='append')
 args=p.parse_args()
 for prime in args.prime or [101]:
  run(prime,q['K0'])
