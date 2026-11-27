"""Good-reduction third-zero unit over the exact reverse-silent parameter."""
from off8_projection import *
import sympy as SY
from flint import nmod_poly
from itertools import permutations
from four_active import U

class Base:
 def __init__(self,p,t,fac):
  self.p=p;self.t=t
  self.M=nmod_poly([self.k(fac.get((j,),K.zero)) for j in range(fac.degree()+1)],p)
  assert self.M.degree()==fac.degree() and int(self.M.leading_coefficient())==1
 def k(self,a):
  x=0
  for c in K.convert(a).to_list():
   x=(x*self.t+int(c.numerator)*pow(int(c.denominator),-1,self.p))%self.p
  return x
 def __call__(self,x):
  if isinstance(x,U):
   assert x.A is self
   return x
  return U((x if isinstance(x,nmod_poly) else nmod_poly([x],self.p))%self.M,self)
def det(a):
 r=0
 for p in permutations(range(len(a))):
  s=(-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))
  for i,j in enumerate(p):s*=a[i][j]
  r+=s
 return r
def cramer(H,b):
 return [det([[b[i] if j==k else x for j,x in enumerate(r)] for i,r in enumerate(H)])
         for k in range(len(H))]
def trim(a):
 r=list(a)
 while r and not r[-1]:r.pop()
 return r
def add(a,b):
 n=max(len(a),len(b));return trim([x+y for x,y in zip(a+[0]*(n-len(a)),b+[0]*(n-len(b)))])
def sc(a,v):return trim([x*v for x in a])
def mul(a,b):
 r=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):r[i+j]+=x*y
 return trim(r)
def qr(a,b):
 assert b[-1]==1
 r=trim(a);p=[0]*max(0,len(a)-len(b)+1)
 while len(r)>=len(b):
  k=len(r)-len(b);U=r[-1];p[k]=U
  for j,V in enumerate(b):r[j+k]-=U*V
  r=trim(r)
 return trim(p),r
def ev(a,x):
 s=0
 for y in a[::-1]:s=s*x+y
 return s
def nodal(pegs):
 r=[1]
 for x in pegs:r=mul(r,[-x,1])
 return r
def multicol(V,G):
 m=len(V)-1
 d=V[-1].A(0)
 C=[qr([0]*i+G,V)[1] for i in range(m)]
 return det([[C[j][i] if i<len(C[j]) else d for j in range(m)] for i in range(m)])

def verify(front,fac,p,t):
 A=Base(p,t,fac);u=A(nmod_poly([0,1],p))
 g=2/(4-(1+2*u-u*u)*(u-2));L=[A(v) for v in (1,-20,90,-140,70)]
 x=1-g;z=x-g*u
 v=1+2*t;w=2-v if front else 2*v;r=0 if front else 3*v*pow(2,-1,p)-1
 a,b=g*(1+v),g*(1+w)
 g1=g*g/2;ha,hb=g*v*g1,g*(w-r)*g1
 q0,q1=ev(L,a)/ha,ev(L,b)/hb
 q1=(q1-q0)/(b-a)
 q0-=a*q1
 xi=-q0/q1
 q=[-xi,A(1)];p0=sc(L,1/q1)
 S,r0=qr(p0,q);Q,r1=qr(S,q)
 assert len(r0)==1 and len(r1)<=1
 d=r0[0];r1=r1[0] if r1 else A(0)
 I=lambda f:sum(A(c)/(j+1) for j,c in enumerate(f))
 lam1=-I(S)/d
 lam2=-(I(mul(S,S))+2*d*(I(Q)+r1*lam1))/(d*d)
 qq=mul(q,q)
 def T(f):
  v,w=qr(f,qq)
  assert len(v)<=8 and len(w)<=2
  w+= [A(0)]*(2-len(w))
  return I(v)+w[0]*lam2+w[1]*(lam1+xi*lam2)
 P4=nodal([a,b,x,z])
 Ts=[T([0]*j+P4) for j in range(6)]
 H=[[Ts[i+j] for j in range(3)] for i in range(3)]
 hdet=det(H)
 Q3=[w/hdet for w in cramer(H,[-Ts[3+i] for i in range(3)])]+[A(1)]
 ta=(g*a**3+g*v*g**3-a**4/4)/ha
 tb=(g*b**3+g*(w-r)*g**3+g*r*a**3-b**4/4)/hb
 ks=(tb-ta)/(b-a)
 C=nodal([g,a,b])
 G=add([A(0)]+[A(v)/(i+1) for i,v in enumerate(C)],sc(C,-g))
 Kt=[ta-ks*a-2*(g+a+b)/3,ks]
 F=add(mul([q0,q1],G),mul(Kt,L))
 F,rem=qr(F,nodal([a,b]))
 assert not rem
 multicol(Q3,F).inv()
 return p,t


if __name__=='__main__':
 p,t=1009,285
 assert SY.isprime(p) and (2*t*t-1)%p==0
 for front in (True,False):
  M,d0,d1=primitive(front)
  assert M.degree()==29 and d0.degree()==d1.degree()==0
  print("Silent trailing third: cubic unit",front,verify(front,M,p,t))
