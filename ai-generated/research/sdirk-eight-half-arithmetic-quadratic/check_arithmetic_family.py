"""Replay the two arithmetic–arithmetic signs through exact guarded finite fibers."""
from arithmetic_projection import *
import literal_front as L
from check_star_family import F, FE, Mod, Split, NonUnit, moment_rank, Lpoly, Rv, norm
import sympy as Y
SY=Y

class SplitY(Exception):
 def __init__(self,u,v):self.vals=(u,v)


class SplitT(Exception):
 def __init__(self,v):self.v=v

class SF(F):
 def __init__(self,M,theta=None):
  super().__init__(M)
  self.theta=theta
 def __call__(self,c):
  if isinstance(c,FE):
   assert c.ctx is self
   return c
  f=E.cast(c)
  if self.theta is not None:
   f=E((f.a+f.b*self.theta)%self.M.a)
  return SE(f%self.M,self)

class SE(FE):
 def testT(self):
  if not self or self.ctx.theta is not None or self.ctx.M.b:return
  M=self.ctx.M.a
  a,b=self.v.a,self.v.b
  if not b or (a*a-b*b/2)%M:return
  d,ib,_=b.xgcd(M)
  assert d.degree()==0
  z=(-a*ib)%M
  assert (z*z-Q(1,2))%M==0
  raise SplitT(z)
 def chk(self):
  self.testT()
  return super().chk()
 def inv(self):
  self.testT()
  if self and not self.v.b and not self.ctx.M.b:
   d,z,_=self.v.a.xgcd(self.ctx.M.a)
   assert d.degree()==0
   return self.ctx(E(z))
  return super().inv()
def guard(f):
 if not f:return False
 if isinstance(f,FE):
  f.chk();return True
 assert isinstance(f,Ext)
 g=f.norm()
 if g:
  assert guard(g)
  return True
 assert f.b and guard(f.b)
 bad=-f.a/f.b
 raise SplitY(bad,-f.ctx.c1-bad)

def div(x,y):
 assert guard(y)
 return x/y

def specialized(M,q,p,pegs,Y0,R0,limit=2350):
 for r0 in Y.primerange(997,limit):
  for t0 in Y.sqrt_mod(pow(2,-1,int(r0)),int(r0),all_roots=True):
   try:
    V=Mod(M,int(r0),int(t0))
    cmap={}
    def vv(t):
     if isinstance(t,Ext):
      R=cmap[t.ctx]
      return R(vv(t.a))+R.gen()*vv(t.b)
     if isinstance(t,Rat):
      return V(E(t.a,t.b))/V(E(t.d))
     return V(t)
    if Y0 is not None:cmap[Y0]=Ring2(vv(Y0.c0),vv(Y0.c1))
    if R0 is not None:cmap[R0]=Ring2(vv(R0.c0),vv(R0.c1))
    Tg,Gs=moment_rank(list(map(vv,pegs)),list(map(vv,q)),list(map(vv,p)))
    for G in Gs+[Gs[0]+Gs[1]+Gs[2],Gs[0]+2*Gs[1]+4*Gs[2]]:
     try:
      V(norm(G)).inv()
      print('arithmetic Hankel unit',M.degree(),r0,t0,flush=True)
      return True
     except NonUnit:pass
   except (NonUnit,ValueError,ZeroDivisionError):
    continue
 return False

def at_y(F0,y,Y0,phi):
 M=F0.M
 a0,b0,hA,hB,Hs,d,W,AU,BU,CU,DU,frontM=L.front_data(False)
 cv=lambda x:F0(Rat.k(x).numerator())
 a,b,ha,hb=map(cv,(a0,b0,hA,hB))
 s=F0(E(P([0,1])))
 ss=s
 def v(f):return sum(cv(w)*s**i*y**j for (i,j,k),w in f.items() if not k)
 for u in (s-a,s-b,y-a,y-b,y-s,v(d)):
  if not guard(u):return 'invalid clock/early rank'
 a1,b1,c1,d1=map(v,(AU,BU,CU,DU))
 h=-div(a1,b1) if b1 else -div(c1,d1) if d1 else None
 if h is None:
  assert a1 or c1
  return 'incompatible raw affine h'
 assert a1+b1*h==0 and c1+d1*h==0
 h_s=v(Hs)
 data=[(a,ha),(b,hb),(s,h_s),(y,h)]
 rows=[Rv(u) for u,h0 in data]
 idx=[0,1,2];D=det([rows[i] for i in idx])
 if not D:
  idx=[0,1,3];D=det([rows[i] for i in idx])
 assert D and guard(D)
 T0,H=data[5-idx[-1]]
 cps=[cramer([rows[i] for i in idx],[data[i][1]*data[i][0]**j for i in idx]) for j in range(3)]
 cp=[[div(sum(row[l]*(Lpoly[l][k] if k<len(Lpoly[l]) else 0) for l in range(3)),D)
      for k in range(6)] for row in cps]
 eq=[ev(r,T0)-H*T0**j for j,r in enumerate(cp)]
 if not eq[0] and not eq[1]:
  assert eq[2]
  return 'no affine monic choice'
 a_i,b_i=(1,0) if eq[1] else (0,1)
 g,b0=-div(eq[2],eq[a_i]),-div(eq[b_i],eq[a_i])
 qq0=[0,0,F0(1)];qq0[a_i]=g
 qq1=[0,0,F0(0)];qq1[a_i]=b0;qq1[b_i]=F0(1)
 pp0=[u+g*v0 for u,v0 in zip(cp[2],cp[a_i])]
 pp1=[u+b0*v0 for u,v0 in zip(cp[b_i],cp[a_i])]
 c,d,k,l,_=L.end(phi,False);c,d,k,l=map(cv,(1-c,1-d,k,l))
 if any(not ev(qq0,u) and not ev(qq1,u) for u in (c,d)):return 'fixed rear pole'
 Ra=mul([ev(x,d) for x in (qq0,qq1)],[ev(x,c) for x in (pp0,pp1)])
 Rb=mul([ev(x,c) for x in (qq0,qq1)],[ev(x,d) for x in (pp0,pp1)])
 Re=trim([l*x-k*w for x,w in zip(Ra+[0]*(3-len(Ra)),Rb+[0]*(3-len(Rb)))])
 assert Re
 if len(Re)==1:return 'constant rear ratio'
 B=None
 if len(Re)==2:be=-div(Re[0],Re[1])
 else:
  B=Ring2(div(Re[0],Re[2]),div(Re[1],Re[2]))
  be=B.gen()
 def take(be):return [u+be*v for u,v in zip(qq0,qq1)],[u+be*v for u,v in zip(pp0,pp1)]
 q,p=take(be)
 rho=ev(p,Ring2(q[0],q[1]).gen()).norm()
 if not rho:return 'entire profile noncoprime'
 if B is not None:
  if not rho.norm():
   assert rho.b
   be=-B.c1+div(rho.a,rho.b)
   q,p=take(be);B=None
   rho=ev(p,Ring2(q[0],q[1]).gen()).norm()
   if not rho:return 'no coprime beta'
  else:assert guard(rho.norm())
 if B is None:assert guard(rho)
 if any(not ev(q,u) for u in (a,b,s,y,c,d)):return 'fixed clock pole'
 if specialized(M,q,p,(a,b,s,y,c,d),Y0,B):return 'Hankel unit'
 return None

def on_scalar(M,sgn,theta=None):
 F0=SF(M,theta)
 a,b,ha,hb,h,d,W,*_=L.front_data(False)
 R=W.exquo(d.exquo((L.s-a)*(L.s-b)))
 s=F0(E(P([0,1])))
 cv=lambda v:F0(Rat.k(v).numerator())
 co=trim([sum(cv(v)*s**i for (i,j,k),v in R.items() if j==j0 and not k) for j0 in range(3)])
 assert co
 if len(co)==1:return [('no y root',1)]
 if len(co)==2:
  return [(at_y(F0,-div(co[0],co[1]),None,sgn),1)]
 Y0=Ring2(div(co[0],co[2]),div(co[1],co[2]))
 try:return [(at_y(F0,Y0.gen(),Y0,sgn),2)]
 except SplitY as e:
  q=[]
  for y in e.vals:
   if all(y!=y0 for y0 in q):q.append(y)
  return [(at_y(F0,y,None,sgn),1) for y in q]

def certify(M,sgn,theta=None):
 try:
  res=on_scalar(M,sgn,theta)
 except SplitT as e:
  assert theta is None
  print("split exact t embedding", M.degree(),flush=True)
  return certify(M,sgn,e.v) and certify(M,sgn,-e.v)
 except Split as e:
  a,b=e.f,M.exact(e.f)
  return certify(a,sgn) and certify(b,sgn)
 print('arithmetic scalar fibers',sgn,M.degree(),res,flush=True)
 return all(x is not None for x,j in res)

def check_exception(rear_sign,M,raw):
 pegs,qs,ps,R,Y=raw
 N=R[2].norm()
 M=M/M.leading_coefficient()
 a,b=N.a%M,N.b%M
 assert a and b and (a*a-b*b/2)%M==0
 d,bb,_=b.xgcd(M)
 assert d.degree()==0 and N.d.gcd(M).degree()==0
 theta=(-a*bb)%M
 assert (theta*theta-Q(1,2))%M==0
 for ell in SY.primerange(997,2500):
  p=int(ell)
  try:
   V=Mod(E(M),p,0)
   t=V(E(theta))
   assert 2*t*t==1
   for ts,exceptional in ((t,True),(-t,False)):
    def sc(u):
     if not isinstance(u,Rat):return V(u)
     return (V(E(u.a))+ts*V(E(u.b)))/V(E(u.d))
    T=Ring2(sc(Y.c0),sc(Y.c1))
    def cv(x,y):
     if not isinstance(x,Ext):return sc(x)
     assert x.ctx is Y
     return sc(x.a)+y*sc(x.b)
    if exceptional:
     a,b=sc(R[2].a),sc(R[2].b)
     y_bad=-a/b
     y_good=-T.c1-y_bad
     assert y_bad*y_bad+T.c1*y_bad+T.c0==0
     assert cv(R[2],y_bad)==0
     ycases=[(y_bad,True),(y_good,False)]
    else:ycases=[(T.gen(),False)]
    for y,linear in ycases:
     c0,c1,c2=[cv(x,y) for x in R]
     if linear:
      assert c2==0
      be=-c0/c1
      f=lambda x:cv(x,y)
     else:
      A=Ring2(c0/c2,c1/c2)
      be=A.gen()
      f=lambda x:A(cv(x,y))
     qs1=[f(u)+be*f(v) for u,v in zip(*qs)]
     ps1=[f(u)+be*f(v) for u,v in zip(*ps)]
     Pg=[f(x) for x in pegs]
     T0,Gs=moment_rank(Pg,qs1,ps1)
     L=Gs+[Gs[0]+Gs[1]+Gs[2],Gs[0]+2*Gs[1]+4*Gs[2]]
     found=False
     for i,G in enumerate(L):
      try:V(norm(G)).inv()
      except NonUnit:continue
      found=True
      print('exact largest split Hankel unit',rear_sign,M.degree(),p,exceptional,linear,i,flush=True)
      break
     if not found:raise NonUnit('no unit in this fiber')
   return True
  except (NonUnit,ZeroDivisionError,ValueError):continue
 return False


if __name__=='__main__':
    signs=(1,-1) if len(sys.argv)==1 else (int(sys.argv[1]),)
    for sign in signs:
        factors,generic,raw=projection(sign)
        pegs,q,p,R,RY=generic
        for M in factors:
            if M.degree()==44:
                assert check_exception(sign,M,raw)
            else:
                assert specialized(E(M),q,p,pegs,RY,R,limit=1020) or certify(E(M),sign)
        print("excluded arithmetic–arithmetic sign",sign,flush=True)
