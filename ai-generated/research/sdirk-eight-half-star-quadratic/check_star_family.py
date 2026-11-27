"""Exact s-fiber splitting; only finite monic algebra unit tests use a prime."""
from star_projection import *
import literal_front as L
from flint import nmod_poly
import sympy as SY

class NonUnit(ArithmeticError):pass
class Split(Exception):
 def __init__(self,f):self.f=f
class F:
 def __init__(self,M): self.M=M.monic()
 def __call__(self,c):
  if isinstance(c,FE):
   assert c.ctx is self
   return c
  return FE(E.cast(c)%self.M,self)
class FE:
 def __init__(self,v,ctx):self.v=v;self.ctx=ctx
 def __bool__(self):return bool(self.v)
 def __eq__(self,x):
  if isinstance(x,Ext):return NotImplemented
  return self.v==self.ctx(x).v
 def __add__(self,x):
  if isinstance(x,Ext):return NotImplemented
  return self.ctx(self.v+self.ctx(x).v)
 __radd__=__add__
 def __neg__(self):return self.ctx(-self.v)
 def __sub__(self,x):
  if isinstance(x,Ext):return NotImplemented
  return self+-self.ctx(x)
 def __rsub__(self,x):
  if isinstance(x,Ext):return NotImplemented
  return self.ctx(x)+-self
 def __mul__(self,x):
  if isinstance(x,Ext):return NotImplemented
  return self.ctx(self.v*self.ctx(x).v)
 __rmul__=__mul__
 def chk(self):
  if not self:raise NonUnit('zero')
  M=self.ctx.M
  if not M.b:
   n=self.v.a*self.v.a-self.v.b*self.v.b/2
   if not n.gcd(M.a).degree():return self
  d=self.v.gcd(M)
  if d.degree()>0:
   assert d.degree()<self.ctx.M.degree()
   raise Split(d)
  return self
 def inv(self):
  if not self:raise NonUnit('zero')
  M=self.ctx.M
  if not M.b:
   n=(self.v.a*self.v.a-self.v.b*self.v.b/2)%M.a
   d,u,_=n.xgcd(M.a)
   if not d.degree():
    w=self.ctx(E(self.v.a*u%M.a,-self.v.b*u%M.a))
    assert w*self==1
    return w
  z,d=self.v.invmod(M)
  if z is not None:return self.ctx(z)
  assert 0 < d.degree()<self.ctx.M.degree()
  raise Split(d)
 def __truediv__(self,x):
  if isinstance(x,Ext):return NotImplemented
  return self*self.ctx(x).inv()
 def __rtruediv__(self,x):
  if isinstance(x,Ext):return NotImplemented
  return self.ctx(x)*self.inv()
 def __pow__(self,n):
  return pow_mul(self,n,1)
 def __repr__(self):return f'FE({self.v.degree()}/{self.ctx.M.degree()})'

def pow_mul(f,n,one):
 assert n>=0
 a=one
 while n:
  if n&1:a=a*f
  n//=2
  if n:f=f*f
 return a

class Mod:
 def __init__(self,M,p,u):
  self.p=p;self.u=u;self.M=self.cast(M)
  assert self.M.degree()==M.degree() and int(self.M.leading_coefficient())==1
 def rc(self,a):
  return int(a.p)%self.p*pow(int(a.q),-1,self.p)%self.p
 def cast(self,x):
  return nmod_poly([(self.rc(x.a[i])+self.u*self.rc(x.b[i]))%self.p
                    for i in range(x.degree()+1)],self.p)
 def __call__(self,f):
  if isinstance(f,MF):
   assert f.ctx is self
   return f
  if isinstance(f,FE):f=f.v
  a=self.cast(E.cast(f)) if not isinstance(f,nmod_poly) else f
  return MF(a%self.M,self)
class MF:
 def __init__(self,v,ctx):self.v=v;self.ctx=ctx
 def __bool__(self):return bool(self.v)
 def __eq__(self,x):
  if isinstance(x,Ext):return NotImplemented
  return self.v==self.ctx(x).v
 def __add__(self,x):
  if isinstance(x,Ext):return NotImplemented
  return self.ctx(self.v+self.ctx(x).v)
 __radd__=__add__
 def __neg__(self):return self.ctx(-self.v)
 def __sub__(self,x):
  if isinstance(x,Ext):return NotImplemented
  return self+-self.ctx(x)
 def __rsub__(self,x):
  if isinstance(x,Ext):return NotImplemented
  return self.ctx(x)+-self
 def __mul__(self,x):
  if isinstance(x,Ext):return NotImplemented
  return self.ctx(self.v*self.ctx(x).v)
 __rmul__=__mul__
 def inv(self):
  d,x,j=self.v.xgcd(self.ctx.M)
  if d.degree()!=0 or not d:raise NonUnit('mod')
  e=self.ctx(x);assert self*e==1
  return e
 def __truediv__(self,x):
  if isinstance(x,Ext):return NotImplemented
  return self*self.ctx(x).inv()
 def __rtruediv__(self,x):
  if isinstance(x,Ext):return NotImplemented
  return self.ctx(x)*self.inv()
 def __pow__(self,n):
  return pow_mul(self,n,1)

L3=lambda x:20*x**3-30*x*x+12*x-1
L4=lambda x:70*x**4-140*x**3+90*x*x-20*x+1
L5=lambda x:252*x**5-630*x**4+560*x**3-210*x*x+30*x-1
Lpoly=((-1,12,-30,20),(1,-20,90,-140,70),(-1,30,-210,560,-630,252))
def Rv(x):return list(f(x) for f in (L3,L4,L5))

def moment_rank(pegs,q,p):
 q2=mul(q,q);qp=mul(q,p);p2=mul(p,p)
 tri=[divmod_monic(f,q2) for f in (qp,[0]+qp,p2,[0]+p2)]
 N=[v+[0]*(4-len(v)) for u,v in tri]
 d=det(N)
 I=lambda f:sum(x*Q(1,i+1) for i,x in enumerate(f))
 co=cramer(N,[-I(u) for u,v in tri])
 P6=[1]
 for y in pegs:P6=mul(P6,[-y,1])
 T=[]
 for j in range(6):
  u,v=divmod_monic([0]*j+P6,q2)
  T.append(d*I(u)+sum(x*y for x,y in zip(co,v)))
 gg=[det([[T[i+j+h] for j in range(3)] for i in range(3)]) for h in range(2)]
 gg+= [det([[T[i+j] for j in (0,1,3)] for i in range(3)])]
 return T,gg

def norm(x):
 while isinstance(x,Ext):x=x.norm()
 return x
def validate(M,pegs,q,p,R,tag):
 for r0 in SY.primerange(997,1500):
  for t0 in SY.sqrt_mod(pow(2,-1,int(r0)),int(r0),all_roots=True):
   try:
    V=Mod(M,int(r0),int(t0))
    if R:
     Z=Ring2(V(R.c0),V(R.c1))
     cv=lambda x:Z(V(x.a))+Z.gen()*V(x.b) if isinstance(x,Ext) else Z(V(x))
    else:cv=V
    poles=[cv(x) for x in pegs]
    g0,g1=map(lambda f:list(map(cv,f)),(q,p))
    # The scaled moment gate is valid here without inverting the residue determinant.
    T,gs=moment_rank(poles,g0,g1)
    for i in range(4):
     w=gs[0]+i*gs[1]+(i*i+1)*gs[2]
     try:
      norm(w).inv()
      print('unit finite gate',tag,M.degree(),r0,t0,i,flush=True)
      return True
     except NonUnit:pass
    for i,w in enumerate(gs):
     try:
      norm(w).inv()
      print('unit pure Hankel gate',tag,M.degree(),r0,t0,i,flush=True)
      return True
     except NonUnit:pass
   except (ValueError,ZeroDivisionError,NonUnit):pass
 return False

def run_fiber(M,rear,sgn,phase):
 C=F(M)
 K=lambda x:C(Rat.k(x).numerator())
 A,B,hA,hB,Hs,d,W,AU,BU,CU,DU,frontM=L.front_data(True)
 aa,bb,ha,hb=map(K,(A,B,hA,hB))
 ss=C(E(P([0,1])))
 y=3*ss/2-C(Q(1,4)) if phase==0 else C(Q(103,72))-ss
 def value(f):
  return sum(K(v)*ss**i*y**j for (i,j,k),v in f.items() if not k)
 for u in [ss-aa,ss-bb,y-aa,y-bb,y-ss,value(d)]:
  if not u:return "twin/early rank"
  u.chk()
 a1,b1,cc1,d1=map(value,(AU,BU,CU,DU))
 hu=-a1/b1 if b1 else -cc1/d1 if d1 else None
 if hu is None:
  assert a1 or cc1
  return "no affine h read"
 assert a1+b1*hu==0 and cc1+d1*hu==0
 hs=value(Hs)
 data=[(aa,ha),(bb,hb),(ss,hs),(y,hu)]
 rows=[Rv(x) for x,h in data]
 idx=(0,1,2)
 d0=det([rows[i] for i in idx])
 if not d0:
  idx=(0,1,3)
  d0=det([rows[i] for i in idx])
 assert d0
 ip=d0.inv()
 other=5-idx[-1]
 Y,H=data[other]
 co=[cramer([rows[i] for i in idx],[data[i][1]*data[i][0]**j for i in idx]) for j in range(3)]
 pp=[[sum(co[k]*(Lpoly[k][i] if i<len(Lpoly[k]) else 0) for k in range(3))*ip for i in range(6)] for co in co]
 U=[ev(p,Y)-H*Y**j for j,p in enumerate(pp)]
 if not U[0] and not U[1]:
  assert U[2]
  return "no monic denominator"
 if U[1]: x1,x0=1,0
 else:x1,x0=0,1
 ide=U[x1].inv()
 ab0=-U[2]*ide;ab1=-U[x0]*ide
 q0=[C(0),C(0),C(1)];q1=[C(0),C(0),C(0)]
 q0[x1]=ab0;q1[x1]=ab1;q1[x0]=C(1)
 p0=[v+w*ab0 for v,w in zip(pp[2],pp[x1])]
 p1=[v+w*ab1 for v,w in zip(pp[x0],pp[x1])]
 c,e,k,l,_=L.end(sgn,rear);c,e,k,l=map(K,(1-c,1-e,k,l))
 Ra=mul([eval_(s,e) for s in (q0,q1)],[eval_(s,c) for s in (p0,p1)])
 Rb=mul([eval_(s,c) for s in (q0,q1)],[eval_(s,e) for s in (p0,p1)])
 if any(not ev(q0,x) and not ev(q1,x) for x in (c,e)):return "fixed rear pole"
 Rq=trim([l*u-k*v for u,v in zip(Ra+[C(0)]*(3-len(Ra)),Rb+[C(0)]*(3-len(Rb)))])
 assert Rq
 if len(Rq)==1:return "rear ratio constant"
 def at_beta(beta):return ([u+beta*v for u,v in zip(q0,q1)],[u+beta*v for u,v in zip(p0,p1)])
 if len(Rq)==2:
  R=None
  q,p=at_beta(-Rq[0]/Rq[1])
 else:
  R=Ring2(Rq[0]/Rq[2],Rq[1]/Rq[2])
  q,p=at_beta(R.gen())
 r=ev(p,Ring2(q[0],q[1]).gen()).norm()
 if not r:return "entire pencil noncoprime"
 if R is not None and not r.norm():
  if not r.b:
   raise AssertionError('zero scalar has zero square but branch should split')
  g=-R.c1+r.a/r.b
  R=None
  q,p=at_beta(g)
  r=ev(p,Ring2(q[0],q[1]).gen()).norm()
  if not r:return "no coprime beta"
 if R is not None:r.norm().chk()
 else:r.chk()
 if any(not ev(q,x) for x in (aa,bb,ss,y,c,e)):return "fixed pole"
 tag=(rear,sgn,phase)
 if validate(C.M,[aa,bb,ss,y,c,e],q,p,R,tag):return "Hankel unit"
 print('residual unexcluded finite fiber',tag,M.degree(),flush=True)
 return None

def eval_(v,x):return ev(v,x)
def solve_fiber(M,rear,sgn,phase):
 try:
  ans=run_fiber(M,rear,sgn,phase)
 except Split as S:
  j=S.f
  assert 0<j.degree()<M.degree()
  return solve_fiber(j,rear,sgn,phase) and solve_fiber(M.exact(j),rear,sgn,phase)
 print('fiber verdict',rear,sgn,phase,M.degree(),ans,flush=True)
 return ans is not None

def ghost_check(Q0,src,limits=2500):
 pegs,q,p,R,rho,base_guards=src
 M=E(Q0/Q0.leading_coefficient())
 rn=rho.norm()
 if rn.d.gcd(M.a).degree()>0:return False
 ra=rn.a%M.a;rb=rn.b%M.a
 res=(ra*ra-rb*rb/2)%M.a
 if res:expected=0
 elif not ra and not rb:expected=M.degree()
 else:
  assert M.degree()%2==0
  expected=M.degree()//2
 for q0 in SY.primerange(997,limits):
  for t0 in SY.sqrt_mod(pow(2,-1,int(q0)),int(q0),all_roots=True):
   def cr(u):
    if isinstance(u,Rat):return V(E(u.a,u.b))/V(E(u.d))
    return V(u)
   try:
    V=Mod(M,int(q0),int(t0))
    if V.M.gcd(V.M.derivative()).degree()!=0:continue
    Z=Ring2(cr(R.c0),cr(R.c1))
    c=lambda u:Z(cr(u.a))+Z.gen()*cr(u.b) if isinstance(u,Ext) else Z(cr(u))
    TT,G=moment_rank(list(map(c,pegs)),list(map(c,q)),list(map(c,p)))
   except (NonUnit,ValueError,ZeroDivisionError):
    continue
   for A in G+[G[0]+G[1]+G[2],G[0]+2*G[1]+4*G[2]]:
    A=Z(A)
    d1=V.M.gcd(A.norm().v).degree()
    d0=V.M.gcd(A.a.v).gcd(A.b.v).degree()
    assert d1+d0>=expected
    if d1+d0==expected:
     print('finite saturated rank',M.degree(),expected,q0,t0,flush=True)
     return True
 return False

if __name__=="__main__":
    import sys
    phases=[(r,e,y) for r,e in ((1,1),(0,1),(0,-1)) for y in (0,1)]
    if len(sys.argv)>1:
        assert len(sys.argv)==4
        phases=[tuple(map(int,sys.argv[1:]))]
    for r,e,y in phases:
        print("star-front phase",r,e,y,flush=True)
        P0=star_pencil(bool(r),e,y)
        for U in project(P0):
            assert ghost_check(U,P0) or solve_fiber(E(U),bool(r),e,y)
        print("excluded star-front phase",r,e,y,flush=True)
