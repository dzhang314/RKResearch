"""Detected-six distinct with both literal front rows active and physical eight active."""
from shared_proxy import transfer
from equal_detected import ends,h4
from unequal_finite import *
from variable_gamma import Lf
from off8_fibers import multicol
from functools import lru_cache

def mon(f):
 assert f
 return sc(f,f[-1].inv())
def subst(f,x):
 return sum_poly([sc(power(x,j),v) for j,v in enumerate(f)])
def intp(F,D,j=0):
 return sum(F(x)/(i+j+1) for i,x in enumerate(D))
def strip(P,guards):
 while True:
  D=gcdp(P,guards)
  if len(D)<=1:break
  P,r=divp(P,D);assert not r
 D=gcdp(P,deriv(P))
 P,r=divp(P,D);assert not r
 return mon(P)

@lru_cache(None)
def model(front,M):
 F=ExField(Epoly(M))
 g=F(E(P([0,1])));X=1/g-1
 cv=lambda v:F(Epoly(JJ(v))) if v else F(0)
 A,B,r=map(cv,ends(front,1));ha,hb=(A-1)/2,(B-1-r)/2
 p=[F(i)*g**j for j,i in enumerate(Lco)]
 qa,qb=ev(p,A)/ha,ev(p,B)/hb;v=(qb-qa)/(B-A)
 q=[qa-A*v,v];R=-q[0]/v
 C,rem=divp(p,q);assert not rem and len(C)==4
 assert X!=R and ev(C,X)
 H4=list(map(cv,pol(h4(front),lambda c:c)))
 return F,g,X,R,A,B,r,ha,hb,p,q,C,H4

def tail_poly(F,X,R,C,rear):
 u=[F(0),F(1)]
 k=[F(1),F(2),F(-1)]
 c=[X,F(-1)]
 d=[X-2,F(1)] if rear else [X,F(-2)]
 Px=ev(C,X)
 H=[F(1)] if rear else [F(-2),F(1),F(4),F(-1)]
 q3=k if rear else add(mul([F(1),F(4),F(-4)],H),[F(0),F(0),F(-8),F(12)])
 S9,T9=subst(C,c),sc(k,Px)
 S8,T8=mul(H,subst(C,d)),sc(q3,Px)
 A9,B9=add(S9,sc(T9,-1)),add(sc(S9,X),sc(mul(c,T9),-1))
 A8,B8=add(S8,sc(T8,-1)),add(sc(S8,X),sc(mul(d,T8),-1))
 return u,k,c,d,H,q3,A9,B9,A8,B8

@lru_cache(None)
def projection(front,M,rear):
 F,g,X,R,A,B,r,ha,hb,p,q,C,H4=model(front,M)
 u,k,c,d,H,q3,A9,B9,A8,B8=tail_poly(F,X,R,C,rear)
 P=add(mul(A9,B8),sc(mul(A8,B9),-1))
 assert P
 D=mul(mul(u,k),mul(add(c,[-R]),add(d,[-R])))
 D=mul(D,mul(add(d,[-X]),add(d,sc(c,-1))))
 D=mul(D,mul(A9,mul(subst(C,c),subst(C,d))))
 P=strip(P,D)
 assert len(P)==(1 if rear else 4)
 print('active8 singleton tail exact projection',front,M.degree(),rear,len(P)-1,flush=True)
 return P

def reduced(M,p,t,tail):
 B0=Bfield(nmod_poly([0,1],p),p,t)
 J0=B0.cast(Epoly(M))
 assert J0.degree()==M.degree() and J0.leading_coefficient()==1
 for J0,m in J0.factor()[1]:
  assert m==1
  B=Bfield(J0,p,t)
  Y=[B(a) for a in tail]
  U=Tower(Y)
  yield U,U.gen()

def fixed_tail(F,X,R,rear,which):
 k=X-R
 return k if which==9 else (2-k if rear else k/2)

def test_moments_base(front,M,rear,which,p,t,verbose=False):
 F,g,X,R,A,B,r,ha,hb,P,Q,C,H4=model(front,M)
 count=int(A==R)+int(B==R)+int(which!=0)
 assert count<=2
 data=(g,X,R,A,B,r,ha,hb,P,Q,C,H4)
 u,k,c,d,H,q3,A9,B9,A8,B8=tail_poly(F,X,R,C,rear)
 if not which:
  W=projection(front,M,rear)
  if len(W)<=1:return True
 else:W=[-fixed_tail(F,X,R,rear,which),F(1)]
 for U,u in reduced(M,p,t,W):
  g,X,R,A,B,r,ha,hb=map(U,data[:8])
  cn,dn=ev(list(map(U,c)),u),ev(list(map(U,d)),u)
  P,Q,C,H4=[list(map(U,T)) for T in data[8:12]]
  # Deduplicate by the exact designated r equality, not accidental mod collisions.
  pegs=[A,B,X,cn,dn]
  if count==0:pegs.append(R)
  if count==2:
   ii=0 if data[3]==data[2] else 1
   pegs.pop(ii)
  D=nodal([g*z for z in pegs])
  J=lambda j:intp(U,D,j)
  if count==0:
   v=J(0);w=J(1)
   try:v.inv()
   except ArithmeticError:w.inv()
  elif count==1:
   (J(0)*J(2)-J(1)**2).inv()
  else:
   a,b,c0,d0=[J(j) for j in range(4)]
   hh=a*c0-b*b
   Y=[(b*d0-c0*c0)/(hh*g**2),(b*c0-a*d0)/(hh*g),U(1)]
   Afn,Bfn=(A8,B8) if which==9 else (A9,B9)
   Afn,Bfn=list(map(U,Afn)),list(map(U,Bfn))
   Z=ev(Bfn,u)/ev(Afn,u)
   E=first5(U,A,B,r,ha,hb,C,H4)
   ev(E,Z).inv()
   multicol(Y,E).inv()
  if verbose:print('orientation passes',front,M.degree(),rear,which,count)
 return True

def first5(U,A,B,m,ha,hb,C,H4):
 h=C
 m0=add([U(-1),U(1)],sc(h,-2))
 m1=add([U(0),U(-1),U(1)/2],sc(h,-2))
 m2=add([U(0),U(0),U(-1),U(1)/3],sc(h,-U(4)/3))
 AA=sum_poly([m2,sc(m1,-A-B),sc(m0,A*B)])
 qha=(hb-ha)/(B-A);qha0=ha-A*qha
 C0,R0=qr(add(H4,[-qha0,-qha]),nodal([A,B]))
 assert not R0 and len(C0)==2
 TA=A**3+A-1-A**4/4
 TB=B**3+B-1-m+m*A**3-B**4/4
 AhA=ha;AhB=hb+m*ha
 def line(a,b):
  B1=(b/hb-a/ha)/(B-A);return [a/ha-A*B1,B1]
 QT=line(TA,TB);QA=line(AhA,AhB)
 T0=sum_poly([[U(0),U(0),U(0),U(1),-U(1)/4],sc(h,2),sc(m2,A+B),sc(m1,-A*B),sc(mul(QT,h),-1)])
 A0=sum_poly([h,sc(m0,qha0),sc(m1,qha),sc(AA,C0[0]),sc(mul(QA,h),-1)])
 return add(A0,sc(T0,-C0[1]))
