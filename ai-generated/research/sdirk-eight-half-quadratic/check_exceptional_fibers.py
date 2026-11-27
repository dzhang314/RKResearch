"""Audit literal rank degeneracies over Q(t), with no degree assumptions at bad fibers."""
from literal_front import *
from functools import reduce
from itertools import product
V,YV,sV=ring('Y,s',K)
J,x=ring('s',K)
def v(f):
    f=R(f)
    assert f.degree(H)<=0
    return V.from_dict({(j,i):c for (i,j,k),c in f.items() if not k})
def w(f):
    f=R(f)
    assert f.degree(H)<=0 and f.degree(Y)<=0
    return J.from_dict({(i,):c for (i,j,k),c in f.items() if not j and not k})
def coeff(f,j):
    return J.from_dict({(i,):c for (i,j0,k),c in f.items() if not k and j0==j})
def res(f,g):return J(v(f).resultant(v(g)))
def Gcd(*args):return reduce(lambda a,b:a.gcd(b),args)
def strip(f,g):
    assert f
    while True:
        j=f.gcd(g)
        if j.degree()<=0:return f.monic()
        f=f.exquo(j)

def profile_legs(x):return (20*x**3-30*x*x+12*x-1,L4(x),252*x**5-630*x**4+560*x**3-210*x*x+30*x-1)

class Nf:
  def __init__(self,M):self.M=M.monic()
  def __call__(self,x0):
    if isinstance(x0,Nu):assert x0.f is self;return x0
    return Nu(J(x0)%self.M,self)
class Nu:
  def __init__(self,x0,f):self.x0,self.f=x0,f
  def __bool__(self):return bool(self.x0)
  def __eq__(self,u):return self.x0==self.f(u).x0
  def __add__(self,u):return self.f(self.x0+self.f(u).x0)
  __radd__=__add__
  def __neg__(self):return self.f(-self.x0)
  def __sub__(self,u):return self+-self.f(u)
  def __rsub__(self,u):return self.f(u)+-self
  def __mul__(self,u):return self.f(self.x0*self.f(u).x0)
  __rmul__=__mul__
  def __truediv__(self,u):return self*self.f(u).inv()
  def inv(self):
    r,_,d=self.x0.gcdex(self.f.M)
    assert d==J.one,(self.x0.as_expr(),self.f.M.as_expr(),d.as_expr())
    ans=self.f(r)
    assert ans*self==1
    return ans
def clean(a):
  a=list(a)
  while a and not a[-1]:a.pop()
  return a
def qr(a,b):
  a=clean(a);b=clean(b);q=[0]*max(0,len(a)-len(b)+1)
  d=b[-1].inv()
  while a and len(a)>=len(b):
    i=len(a)-len(b);u=d*a[-1];q[i]=u
    for j,v in enumerate(b):a[i+j]-=u*v
    a=clean(a)
  return clean(q),a
def gcd_mod_y(a,b):
  a=clean(a);b=clean(b)
  while b:a,b=b,qr(a,b)[1]
  if not a:return []
  d=a[-1].inv()
  return [u*d for u in a]
def mul_y(a,b):
  if not a or not b:return []
  c=[0]*(len(a)+len(b)-1)
  for i,u in enumerate(a):
    for j,v in enumerate(b):c[i+j]+=u*v
  return clean(c)
def no_valid_y(S,U,eq,guards):
  if S.degree()<=0:return
  # Test each irreducible mono component; the generic resultants only locate s.
  for M,e in S.factor_list()[1]:
    F=Nf(M)
    convert=lambda P:clean([F(coeff(P,i)) for i in range(P.degree(Y)+1)]) if P else []
    Y0=convert(U)
    assert Y0 # audited quadratic non-drop of all coefficients simultaneously
    Y1=reduce(gcd_mod_y,map(convert,eq),Y0)
    if len(Y1)<=1:continue
    X=reduce(mul_y,map(convert,guards),[F(1)])
    # Every common root is in the zero set of the product of the guards.
    A=[F(1)]
    for _ in range(len(Y1)-1):A=qr(mul_y(A,X),Y1)[1]
    assert not A,(M.degree(),len(Y1)-1)

def audit_all(front):
 a,b,ha,hb,hs,d,W,A,B,C,D,M=front_data(front)
 v0=d.exquo((s-a)*(s-b))
 U=W.exquo(v0)
 assert Gcd(*(coeff(U,j) for j in range(3))).degree()==0
 guard=w(d)
 # early rank degeneracy
 _,_,_,_,u32=end(1,front)
 E=[[K.one,K.one,K.one],[g,a,b],[g*g-la*g1,a*a,b*b]]
 ts=[T/det(E) for T in cramer(E,[s-g,s*s/2-g*s,s**3/3-g*s*s])]
 ah=[g*ha,u32*ha+g*hb,ts[1]*ha+ts[2]*hb+g*hs]
 j=det([r[:2]+[v] for r,v in zip(M,ah)])
 assert Gcd(w(j),w(v0)).degree()==0
 assert strip(Gcd(res(B,D),res(A,B),res(C,D)),guard).degree()==0
 ds=det([profile_legs(z) for z in (a,b,s)]).exquo((s-a)*(s-b))
 assert strip(Gcd(w(ds),res(U,ds.compose(s,Y))),guard).degree()==0
 rows=[list(profile_legs(z)) for z in (a,b,s,Y)]
 pro=[]
 for i,(nc,dc) in enumerate(((A,B),(C,D))):
  T=[]
  twin=(s-a)*(s-b)*(Y-a)*(Y-b)*(Y-s)
  for j in range(3):
   Tj=det([row+[h*z**j*dc] for row,h,z in zip(rows[:3],(ha,hb,hs),(a,b,s))]+
          [rows[3]+[-nc*Y**j]])
   T.append(Tj.exquo(twin))
  S0=strip(Gcd(*(res(U,N) for N in T)),guard)
  print("exact affine-pencil test",front,i,S0.degree(),flush=True)
  no_valid_y(S0,U,T,[dc,Y-a,Y-b,Y-s])
  pro.append((nc,dc,T))
 return a,b,ha,hb,hs,d,U,pro

def rear_audit(front,rear,sign,data):
 a,b,ha,hb,hs,d,U,pro=data
 c,e,k,l,_=end(sign,rear);c=1-c;e=1-e
 guard=w(d)
 for i,(nc,dc,T) in enumerate(pro):
  rows=[
    list(profile_legs(z))+[-h,-h*z,-h*z*z]
    for z,h in zip((a,b,s),(ha,hb,hs))]
  rows.append([dc*q for q in profile_legs(Y)]+[nc,nc*Y,nc*Y*Y])
  Qc=[0,0,0,1,c,c*c];Qd=[0,0,0,1,e,e*e]
  Pc=list(profile_legs(c))+[0,0,0];Pd=list(profile_legs(e))+[0,0,0]
  L=[0,0,0,0,0,1]
  twin=(s-a)*(s-b)*(Y-a)*(Y-b)*(Y-s)
  def D(v,w):return det(rows+[v,w]).exquo(twin)
  q0=D(Qc,Qd);c0=D(Qc,Pc);d0=D(Qd,Pd)
  mid=l*D(Pc,Qd)-k*D(Qc,Pd)
  D0=D(Qc,L);M0=D(Qd,L)
  G0=l*M0*D(Pc,L)-k*D0*D(Pd,L)
  G1=l*M0*c0-k*D0*D(Qc,Pd)
  xguard=[dc,Y-a,Y-b,Y-s]
  for eq,xg in (([c0,d0,mid],xguard+[q0]),([q0,G0,G1],xguard+[D0,M0])):
   vals=[res(U,N) for N in eq]
   S0=strip(Gcd(*vals),guard)
   print("exact rear-pencil test",front,rear,sign,i,S0.degree(),flush=True)
   no_valid_y(S0,U,eq,xg)

if __name__ == '__main__':
    for front in (True,False):
        data=audit_all(front)
        for rear,sign in product((True,False),(1,-1)):
            if rear and sign==-1:
                continue
            rear_audit(front,rear,sign,data)
    print("All literal row-five and rear-pencils have finite fibers.")

# A common-factor discrepancy supported at a single clock would be
# Gauss. The four corner clocks never are, in either orientation.
for star,sgn in product((True,False),(1,-1)):
    a,b,*_=end(sgn,star)
    assert all(L4(v) != K.zero for v in (a,b,1-a,1-b))
