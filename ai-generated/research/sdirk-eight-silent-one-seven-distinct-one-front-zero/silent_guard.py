"""Exact finite removal of the nonphysical H4=0 stage-four roots."""
from off_literal_active8 import *

class SplitAt(Exception):
 def __init__(self,d):self.d=d

class ExactV(V):
 def inv(self):
  if not self.x:raise ArithmeticError('exact zero pivot')
  G=gcdp(self.A.F,self.x)
  if len(G)>1:
   assert len(G)<len(self.A.F)
   raise SplitAt(G)
  return super().inv()

class ExactField(Nested):
 def __init__(self,G):self.F,self.B=G,F2
 def __call__(self,x):
  if isinstance(x,ExactV) and x.A is self:return x
  return ExactV(qr(x if isinstance(x,list) else [self.B(x)],self.F)[1],self)

@lru_cache(None)
def h4_bad(front):
 H4=[cv(F2,v) for v in pol(h4(front),lambda q:q)]
 L=sum(v*(g*s)**i for i,v in enumerate(Lco))
 return mon(exact_g(can(term(H4,s).resultant(L,1)))),H4

def exact_allowed(G,Phi,H4):
 F=ExactField(G);gg=F.gen()
 T=eval_s(Phi,F,gg,F(0));assert T
 H=list(map(F,H4))
 while True:
  U=gcdp(T,H)
  if len(U)<=1:break
  T,e=qr(T,U);assert not e
 return [list(F(v).x) for v in T]

def h4_splits(G,Phi,H4):
 try:Y=exact_allowed(G,Phi,H4)
 except SplitAt as pp:
  A=mon(pp.d);B,e=qr(G,A);assert not e
  return h4_splits(A,Phi,H4)+h4_splits(B,Phi,H4)
 return [(G,Y)]

def split_h4(gam,phi,front):
 gam=list(gam)
 B,H4=h4_bad(front)
 A=gcdp(gam,B);C=mon(guarded(gam,[B]))
 L=h4_splits(mon(A),phi,H4) if len(A)>1 else []
 print('silent exact H4 guard factors',front,len(A)-1,len(C)-1,[(len(K)-1,len(Y)-1) for K,Y in L],flush=True)
 return C,L

def explicit_fields(J,T,p,t):
 B=Bfield(nmod_poly([0,1],p),p,t)
 M=nmod_poly([int(B(q).x[0]) for q in J],p)
 assert M.degree()==len(J)-1 and M.leading_coefficient()==1
 for M0,_ in M.factor()[1]:
  F=Bfield(M0,p,t);gg=F(nmod_poly([0,1],p))
  v=[ev(list(map(F,x)),gg) for x in T]
  assert not v or v[-1]
  if len(v)==1:v[0].inv();continue
  U=Tower(mon(v));s0=U.gen()
  yield U,U(gg),s0
