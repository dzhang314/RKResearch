"""Exact diagonal/front clock, finite reverse gap, and the seven-active moment gate."""
from variable_gamma import *
from check_star_family import F as ExField,FE,E,P,Q
from flint import nmod_poly
from four_active import U
from off8_fibers import det,trim,add,sc,mul,qr,ev,nodal
import sympy as SY
from itertools import product,combinations

Lco=(1,-20,90,-140,70)
def pol(a,f):return [f(a.get((i,),K.zero)) for i in range(a.degree()+1)]
def exact_coeff(v):return [(int(c.numerator),int(c.denominator)) for c in K.convert(v).to_list()][::-1]
def Epoly(f):
 l=pol(f,exact_coeff)
 return E(P([Q(*a[0]) if len(a)>0 else Q(0) for a in l]),P([Q(*a[1]) if len(a)>1 else Q(0) for a in l]))
def divp(a,b):
 d=b[-1].inv()
 x,r=qr(a,sc(b,d))
 return sc(x,d),r
def gcdp(a,b):
 a,b=trim(a),trim(b)
 while b:a,b=b,divp(a,b)[1]
 return sc(a,a[-1].inv()) if a else []
def deriv(f):return [(j+1)*x for j,x in enumerate(f[1:])]
def exact_fifth(front):
 F,_,_,_,L,A,B=defs(front)
 F0=ExField(Epoly(F))
 g=F0(E(P([0,1])))
 cv=lambda a:F0(Epoly(JJ(a)))
 a,b,ha,hb,sg,*_=phases(front);a,b,ha,hb,sg=map(cv,(a,b,ha,hb,sg))
 LA=[cv(i)*g**j*a**j for j,i in enumerate(Lco)]
 lb=ev(LA,b/a) # equals L4(g b)
 la=sum(LA)
 f1=[cv(i)*g**j for j,i in enumerate(Lco)]
 clos=add(sc(mul(pol(B,cv),f1),(b-a)*ha*hb),mul(pol(A,cv),[b*hb*la-a*ha*lb,ha*lb-hb*la]))
 dd=gcdp(clos,pol(L,cv))
 assert len(dd)==2
 zz=-dd[0]/dd[1]
 hs=-ev(pol(A,cv),zz)/ev(pol(B,cv),zz)
 assert hs and (zz==1 if front else zz!=1)
 return F,F0,(g,a,b,ha,hb,sg,zz,hs)

def exact_tail(front,rear,model):
 H,F,(g,a,b,ha,hb,sg,z0,h0)=model
 u=[F(0),F(1)];k=[F(1),F(2),F(-1)]
 a,b,s=a*g,b*g,z0*g;ha,hb,hs=ha*g**3,hb*g**3,h0*g**3
 L=list(map(F,Lco))
 Qa,Qb=ev(L,a)/ha,ev(L,b)/hb
 Q1=(Qb-Qa)/(b-a);Q0=Qa-a*Q1
 qf=[Q0,Q1]
 x=1-g;c=[x,-g]
 spec=lambda h,f:sum_poly([sc(power(f,i),x) for i,x in enumerate(h)])
 Dx,Qx=ev(L,x),ev(qf,x)
 Dc,Qc=spec(L,c),spec(qf,c)
 if rear is None:
  d=add([x],sc(mul(k,[F(-2),F(1)]),g/2))
  Qd=spec(qf,d)
  A=mul(add([x],sc(d,-1)),sc(Dc,Qx))
  B=mul(k,mul(add(c,sc(d,-1)),sc(Qc,Dx)))
  N=add(A,sc(B,-1))
  guards=u
 else:
  w=[F(2),F(-1)] if rear else [F(0),F(2)]
  d=add([x],sc(w,-g));Qd=spec(qf,d);Dd=spec(L,d)
  den=[F(-2),F(1),F(4),F(-1)] if not rear else [F(1)]
  q3=k if rear else add(mul([F(1),F(4),F(-4)],den),[F(0),F(0),F(-8),F(12)])
  J=sc(mul(mul(mul(k,u),Dd),Qc),Qx)
  A=sc(mul(mul(k,add(u,sc(w,-1))),Qc),Dx)
  B=sc(mul(w,Dc),Qx)
  N=mul(k,add(mul(den,J),sc(mul(mul(q3,add(A,B)),Qd),-1)))
  guards=mul(u,nodal([F(1),F(2)])) if rear else mul(u,den)
 assert N
 D=gcdp(N,guards)
 while len(D)>1:
  N,r=divp(N,D);assert not r
  D=gcdp(N,guards)
 D=gcdp(N,deriv(N))
 N,r=divp(N,D);assert not r
 N=sc(N,N[-1].inv())
 print("tail polynomial",front,rear,"degree",len(N)-1,flush=True)
 return H,N,(g,a,b,s,ha,hb,hs,sg,x,qf)

def power(a,n):
 r=[a[0].A(1)] if isinstance(a[0],U) else [1]
 for _ in range(n):r=mul(r,a)
 return r
def sum_poly(ds):
 r=[]
 for d in ds:r=add(r,d)
 return r
class Bfield:
 def __init__(self,M,p,t):self.M,self.p,self.t=M,p,t
 def cast(self,e):
  g=lambda d:int(d.p)*pow(int(d.q),-1,self.p)
  return nmod_poly([(g(e.a[j])+self.t*g(e.b[j]))%self.p for j in range(e.degree()+1)],self.p)
 def __call__(self,x):
  if isinstance(x,U):assert x.A is self;return x
  if isinstance(x,FE):x=self.cast(x.v)
  if isinstance(x,E):x=self.cast(x)
  return U((x if isinstance(x,nmod_poly) else nmod_poly([x],self.p))%self.M,self)
class Tower:
 def __init__(self,F):
  self.F,self.B=F,F[-1].A
  assert len(F)>1 and F[-1]==1
 def gen(self):return self([self.B(0),self.B(1)])
 def __call__(self,x):
  if isinstance(x,V):assert x.A is self;return x
  return V(qr(x if isinstance(x,list) else [self.B(x)],self.F)[1],self)
class V:
 def __init__(self,x,A):self.x,self.A=x,A
 def __bool__(self):return bool(self.x)
 def __eq__(self,x):return self.x==self.A(x).x
 def __add__(self,y):return self.A(add(self.x,self.A(y).x))
 __radd__=__add__
 def __neg__(self):return self.A(sc(self.x,-1))
 def __sub__(self,x):return self+-self.A(x)
 def __rsub__(self,x):return self.A(x)+-self
 def __mul__(self,x):return self.A(mul(self.x,self.A(x).x))
 __rmul__=__mul__
 def __pow__(self,n):return self.A(power(self.x,n)) if self.x else self.A(0 if n else 1)
 def inv(self):
  a,b=self.A.F,self.x;c,d=[],[self.A.B(1)]
  while b:
   p,r=divp(a,b);a,b=b,r;c,d=d,add(c,sc(mul(p,d),-1))
  if len(a)!=1:raise ArithmeticError('nonunit')
  y=self.A(sc(c,a[0].inv()));assert y*self==1
  return y
 def __truediv__(self,y):return self*self.A(y).inv()
 def __rtruediv__(self,y):return self.A(y)*self.inv()

def det3(T):
 return T[0]*T[2]*T[4]+2*T[1]*T[2]*T[3]-T[0]*T[3]**2-T[1]**2*T[4]-T[2]**3

def moment(U,pts,rf,count=5):
 L=list(map(U,Lco));v=rf[1];xi=-rf[0]/v
 q=[-xi,U(1)];p0=sc(L,1/v)
 S,r0=qr(p0,q);P,r1=qr(S,q)
 assert len(r0)==1 and len(r1)<=1
 d=r0[0];r1=r1[0] if r1 else U(0)
 I=lambda f:sum(U(c)/(j+1) for j,c in enumerate(f))
 l1=-I(S)/d
 l2=-(I(mul(S,S))+2*d*(I(P)+r1*l1))/(d*d)
 q2=mul(q,q)
 G=nodal(pts)
 T=[]
 for j in range(count):
  A,b=qr([0]*j+G,q2);b+=[U(0)]*(2-len(b))
  T.append(I(A)+b[0]*l2+b[1]*(l1+xi*l2))
 return T

def verify7(front,rear,data,p0,t0):
 M,F,vals=data
 p=int(p0);t=int(t0)
 E0=Epoly(M)
 B0=Bfield(nmod_poly([0,1],p),p,t)
 Md=B0.cast(E0)
 assert Md.degree()==M.degree() and Md.leading_coefficient()==1
 for f,n in Md.factor()[1]:
  assert n==1
  B=Bfield(f,p,t)
  N=[B(x) for x in F]
  U=Tower(N)
  g,a,b,s,ha,hb,hs,sg,x,Qf=vals
  g,a,b,s,x=map(U,(g,a,b,s,x));Qf=list(map(U,Qf))
  u=U.gen();c=x-g*u
  if rear is None:
   P=[a,b,s,c,x]
   det3(moment(U,P,Qf)).inv()
  else:
   d=x-g*(2-u if rear else 2*u)
   for fb in combinations((a,b,s),2):
    P=[*fb,c,d,x]
    det3(moment(U,P,Qf)).inv()
 return True

def main():
 for front in (True,False):
  m=exact_fifth(front)
  for rear in (None,True,False):
   d=exact_tail(front,rear,m)
   for p in SY.primerange(997,2450):
    for t in SY.sqrt_mod(pow(2,-1,int(p)),int(p),all_roots=True):
     try:verify7(front,rear,d,p,t)
     except (ArithmeticError,ValueError):continue
     print("excluded seven active phase",front,rear,p,t,flush=True)
     break
    else:continue
    break
   else:print("seven-active unresolved",front,rear,flush=True)
if __name__=='__main__':main()
