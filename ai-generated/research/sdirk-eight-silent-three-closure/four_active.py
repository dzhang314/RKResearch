"""Three invisible rows, four active Gauss clocks: monic cubic unit receipt."""
from flint import nmod_poly
from itertools import product,permutations
import sympy as SY

class Algebra:
 def __init__(self,p,M):
  self.p=p
  self.M=M*pow(int(M.leading_coefficient()),-1,p)
  assert self.M.degree()==3 and int(self.M.leading_coefficient())==1
 def __call__(self,x):
  if isinstance(x,U):
   assert x.A is self
   return x
  return U((x if isinstance(x,nmod_poly) else nmod_poly([x],self.p))%self.M,self)
class U:
 def __init__(self,x,A):self.x,self.A=x,A
 def __bool__(self):return bool(self.x)
 def __eq__(self,u):return self.x==self.A(u).x
 def __add__(self,u):return self.A(self.x+self.A(u).x)
 __radd__=__add__
 def __neg__(self):return self.A(-self.x)
 def __sub__(self,u):return self+-self.A(u)
 def __rsub__(self,u):return self.A(u)+-self
 def __mul__(self,u):return self.A(self.x*self.A(u).x)
 __rmul__=__mul__
 def __pow__(self,n):return self.A(self.x**n)
 def inv(self):
  d,u,_=self.x.xgcd(self.A.M)
  if d.degree()!=0 or not d:raise ArithmeticError(d.degree())
  z=self.A(u)
  assert z*self==1
  return z
 def __truediv__(self,u):return self*self.A(u).inv()
 def __rtruediv__(self,u):return self.A(u)*self.inv()
def scalars(p,x,g):
 I=lambda d:pow(d,-1,p)
 return [(x**(j+1)*I(j+1)-g*x**j)%p for j in range(4)]
def taps(xs,ms):
 # Read all four coefficients by the three-root Lagrange cardinal.
 out=[]
 for i,x in enumerate(xs):
  p=[x.A(1)]
  den=x.A(1)
  for j,y in enumerate(xs):
   if i==j:continue
   den*=x-y
   o=[x.A(0)]*(len(p)+1)
   for k,u in enumerate(p):o[k]-=u*y;o[k+1]+=u
   p=o
  out.append(sum(x*y for x,y in zip(p,ms))/den)
 return out
def gauss3(x):return 20*x**3-30*x*x+12*x-1
def prove(p,t,g,star,roots):
 I=lambda d:pow(int(d)%p,-1,p)
 P=lambda xs:nmod_poly(xs,p)
 X=P([0,1]);L=P([1,-20,90,-140,70])
 A=2+2*t;B=2-2*t if star else 3+4*t
 a,b=g*A%p,g*B%p
 u=1+2*t;w=2-u if star else 2*u;r=0 if star else 3*u*I(2)-1
 a21,a31,a32=g*u%p,g*(w-r)%p,g*r%p
 g1=g*g*I(2)%p
 ha,hb=a21*g1%p,a31*g1%p
 Q0=int(L(a))*I(ha)%p;Q1=int(L(b))*I(hb)%p
 Q=Q0+(X-a)*((Q1-Q0)*I(b-a)%p)
 assert Q.gcd(L).degree()==0
 TA=(g*a**3+a21*g**3-a**4*I(4))*I(ha)%p
 TB=(g*b**3+a31*g**3+a32*a**3-b**4*I(4))*I(hb)%p
 K=TA+(X-a)*((TB-TA)*I(b-a)%p)-2*(g+a+b)*I(3)
 C=(X-g)*(X-a)*(X-b)
 G=P([0]+[int(C[j])*I(j+1)%p for j in range(4)])-g*C
 F,R=divmod(Q*G+K*L,(X-a)*(X-b))
 assert not R and F.degree()==3
 Z=Algebra(p,F)
 z=Z(X);h=Z(L)/Z(Q)
 ns=list(map(Z,(g,a,b)))+[z]
 # Every Vandermonde and active trace divisor has its unit checked before use.
 pa=[Z(0),Z((a-g)*ha),Z((b-g)*hb),(z-g)*h]
 def read(t,x):
  ta=Z(g*x**3*x-x**5*I(5))+sum(u*y**4 for u,y in zip(t,ns))
  ap=sum(u*v for u,v in zip(t,pa))
  return ta,ap
 rest=[x for x in roots if x!=(1-g)%p]
 assert len(rest)==3 and g in rest
 for x,y in permutations(rest,2):
  l3x,l3y=gauss3(x)%p,gauss3(y)%p
  assert l3x and l3y
  u,v=taps(ns,scalars(p,x,g)),taps(ns,scalars(p,y,g))
  t1,h1=read(u,x);t2,h2=read(v,y)
  M,N=l3x*t2-l3y*t1,l3x*h2-l3y*h1
  if x==g:
   assert Z.M.gcd(M.x).gcd(N.x).degree()==0
  else:
   r=taps(ns,[x**j%p for j in range(4)])
   var=(Z(x**4)-sum(q*a0**4 for q,a0 in zip(r,ns)))*l3x
   t=-M/var
   G0=N-t*l3x*sum(q*a0 for q,a0 in zip(r,pa))
   assert Z.M.gcd(G0.x).degree()==0
 return True


def main():
 p,t=1129,203
 assert SY.isprime(p) and (2*t*t-1)%p==0
 L=nmod_poly([1,-20,90,-140,70],p)
 roots=[int(v) for v,m in L.roots() if m==1]
 assert sorted(roots)==[100,214,916,1030]
 for g,star in product(roots,(True,False)):
  assert prove(p,t,g,star,roots)
 print("Both front phases and all 48 ordered Gauss pairs excluded.")
if __name__=='__main__':main()
