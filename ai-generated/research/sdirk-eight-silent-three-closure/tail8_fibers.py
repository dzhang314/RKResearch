"""Monic cubic parameter tower for the fully active three-row tail."""
from tail8_projection import exact_phase,K
from off8_fibers import Base,det,trim,add,sc,mul,qr,ev,nodal
from flint import nmod_poly
from itertools import product
import sympy as SY

class Cube:
 def __init__(self,F):
  self.F=F
  self.A=F[-1].A
  self.n=len(F)-1
  assert self.n>=1 and F[-1]==1
 def __call__(self,u):
  if isinstance(u,C):
   assert u.A is self
   return u
  return C([self.A(u)]+[self.A(0)]*(self.n-1),self)
 def z(self):
  if self.n==1:return self(-self.F[0])
  return C([self.A(0),self.A(1)]+[self.A(0)]*(self.n-2),self)
class C:
 def __init__(self,x,A):self.x,self.A=x,A
 def __bool__(self):return any(self.x)
 def __eq__(self,y):return self.x==self.A(y).x
 def __neg__(self):return C([-u for u in self.x],self.A)
 def __add__(self,y):return C([u+v for u,v in zip(self.x,self.A(y).x)],self.A)
 __radd__=__add__
 def __sub__(self,y):return self+-self.A(y)
 def __rsub__(self,y):return self.A(y)+-self
 def __mul__(self,y):
  d=self.A.A
  c=qr(mul(self.x,self.A(y).x),self.A.F)[1]
  return C(c+[d(0)]*(self.A.n-len(c)),self.A)
 __rmul__=__mul__
 def __pow__(self,n):
  r=self.A(1)
  for k in range(n):r*=self
  return r
 def norm(self):
  col=[(self*self.A.z()**i).x for i in range(self.A.n)]
  return det([[col[j][i] for j in range(self.A.n)] for i in range(self.A.n)])
 def __truediv__(self,y):
  y=self.A(y)
  assert not any(y.x[1:])
  return C([u/y.x[0] for u in self.x],self.A)
 def __rtruediv__(self,y):return self.A(y)/self

def verify(front,rear,data,p,t):
 M,F,H,n=data
 A=Base(p,t,M)
 gamma=A(nmod_poly([0,1],p))
 def cv(x):return A(A.k(x))
 ucoeff=lambda f,j:sum(cv(k)*gamma**i for (j0,i),k in f.items() if j0==j)
 F0=[ucoeff(F,j) for j in range(n+1)]
 Q=Cube([s/F0[-1] for s in F0])
 u=Q.z()
 g=Q(gamma);L=[Q(i) for i in (1,-20,90,-140,70)]
 v=1+2*t;w=2-v if front else 2*v;r=0 if front else 3*v*pow(2,-1,p)-1
 x=1-g;c=x-g*u
 dd=x-g*(2-u if rear else 2*u)
 a,b=g*(1+v),g*(1+w);g1=g*g/2
 ha,hb=g*v*g1,g*(w-r)*g1
 h0,h1=ev(L,a)/ha,ev(L,b)/hb
 l1=(h1-h0)/(b-a);l0=h0-a*l1
 xi=-l0/l1;q=[-xi,Q(1)];pp=sc(L,1/l1)
 S,r0=qr(pp,q);U,r1=qr(S,q)
 assert len(r0)==1 and len(r1)<=1
 d=r0[0];r1=r1[0] if r1 else Q(0)
 I=lambda f:sum(Q(c)/(j+1) for j,c in enumerate(f))
 m1=-I(S)/d
 m2=-(I(mul(S,S))+2*d*(I(U)+r1*m1))/(d*d)
 qq=mul(q,q)
 def T(f):
  v,w=qr(f,qq)
  assert len(v)<=8 and len(w)<=2
  w+= [Q(0)]*(2-len(w))
  return I(v)+w[0]*m2+w[1]*(m1+xi*m2)
 N=nodal([a,b,c,dd,x])
 y=[T([0]*j+N) for j in range(5)]
 W0=det([[y[i+j] for j in range(3)] for i in range(3)])
 H0=sum(Q(cv(k))*u**i*g**j for (i,j),k in H.items())
 (H0+W0).norm().inv()
 return True

def split_polynomial(M,F,H):
 from tail8_projection import J,u
 coeff=lambda f,n:J.from_dict({(j,):k for (i,j),k in f.items() if i==n})
 for n in range(F.degree(u),-1,-1):
  w=M.gcd(coeff(F,n))
  if w.degree()==M.degree():continue
  if w.degree()>0:
   return split_polynomial(w,F,H)+split_polynomial(M.exquo(w).monic(),F,H)
  if n==0:return []
  return [(M,F,H,n)]
 assert H
 return split_polynomial(M,H,F)

if __name__=='__main__':
 p,t=1009,285
 assert SY.isprime(p) and (2*t*t-1)%p==0
 for front,rear in product((True,False),repeat=2):
  M,F,H,q0,q1,qres=exact_phase(front,rear)
  assert M.gcd(q1*qres).degree()==0
  assert M.degree()=={(True,True):26,(True,False):73,(False,True):31,(False,False):68}[front,rear]
  fibers=split_polynomial(M,F,H)
  assert sorted([(ar[0].degree(),ar[-1]) for ar in fibers])==[(8,2),(M.degree()-8,3)]
  for ar in fibers:
   assert verify(front,rear,ar,p,t)
   print("Active trailing third: monic unit",front,rear,ar[0].degree(),ar[-1])
