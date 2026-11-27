"""All-active zero-site, three invisible stages, diagonal one-half."""
import sympy as SY
from sympy.polys.rings import ring
from itertools import product
K=SY.QQ.algebraic_field(SY.sqrt(2)/2)
R,X=ring("X",K)
t=K.unit;half=K.one/2
L4=70*X**4-140*X**3+90*X**2-20*X+1
I=lambda p:sum(v/(i+1) for (i,),v in p.items())
eval_=lambda p,w:p.evaluate(X,w)
def end(star,sign,gamma):
 u=1+2*sign*t;w=2-u if star else 2*u;r=K.zero if star else 3*u/2-1
 g1=gamma*gamma/2
 a,b=gamma*(1+u),gamma*(1+w)
 return a,b,gamma*u*g1,gamma*(w-r)*g1
def scalar_project(front,gamma):
 a,b,ha,hb=end(front,1,gamma)
 r=eval_(L4,a)/ha;s=eval_(L4,b)/hb
 m=(s-r)/(b-a);Q=r+(X-a)*m
 return a,b,Q
def det3(z):return z[0]*z[2]*z[4]+2*z[1]*z[2]*z[3]-z[0]*z[3]**2-z[1]**2*z[4]-z[2]**3
def run():
 for front in (True,False):
  a,b,Q=scalar_project(front,half)
  assert Q.degree()==1 and Q.gcd(L4).degree()==0
  xi=-Q[(0,)]/Q[(1,)]
  q=X-xi;p=L4/Q[(1,)]
  S,r0=p.div(q);u,r1=S.div(q)
  r0,r1=r0.get((0,),K.zero),r1.get((0,),K.zero)
  assert r0
  s1=-I(S)/r0
  s2=-(I(S*S)+2*r0*(I(u)+r1*s1))/(r0*r0)
  def T(F):
   v,w=F.div(q*q)
   assert v.degree()<=7
   return I(v)+w.get((0,),K.zero)*s2+w.get((1,),K.zero)*(s1+xi*s2)
  for rear,sgn in product((True,False),(1,-1)):
   c,d,*_=end(rear,sgn,half);c,d=1-c,1-d
   pp=[a,b,c,d,half]
   assert len(set(pp))==5
   P=R.one
   for v in pp:
    assert eval_(q,v)
    P*=X-v
   r=det3([T(P*X**j) for j in range(5)])
   assert r
   print('active trailing third excluded',front,rear,sgn)
  for sgn in (1,-1):
   z=1-half*(2+2*sgn*t)
   h0=eval_(L4,half)/eval_(Q,half)
   h9=eval_(L4,z)/eval_(Q,z)
   assert h9-2*(1+2*sgn*t)**2*h0
   print('silent trailing third excluded',front,sgn)
if __name__=='__main__':run()
