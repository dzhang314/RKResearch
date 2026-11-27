"""Exact removal of the nonphysical zero-defect fourth row from finite front fibers."""
from nong_front import *

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
class ExactFiber(Nested):
 def __init__(self,G):self.F,self.B=G,B0
 def __call__(self,x):
  if isinstance(x,ExactV) and x.A is self:return x
  return ExactV(qr(x if isinstance(x,list) else [self.B(x)],self.F)[1],self)

def canonical_s(W,Q):
 G={}
 u=W.gen()
 for (i,j,k),v in parts(Q).items():
  assert not i
  G[j]=G.get(j,W(0))+W(v)*u**k
 return trim([G.get(j,W(0)) for j in range(max(G,default=-1)+1)])

@lru_cache(None)
def bad_diag(front,slot):
 H4=core(front,slot)[8];H=term(H4,s)
 Q=term(PX,g*s)
 M=coeff1(can(H.resultant(Q,1)),2)
 return mon(M)
def allowed(front,slot,M,flags):
 W=ExactFiber(M)
 ph=canonical_s(W,core(front,slot)[0])
 h4=list(map(W,core(front,slot)[8]))
 cv=lambda a:B0(Epoly(JJ(a))) if a else B0(0)
 a=W(cv(ends(front,1)[slot]));R=W(R0)/W.gen()
 for k,q in (('r',R),('a',a)):
  if k in flags:
   ph,rem=qr(ph,[-q,W(1)])
   assert not rem
 if len(ph)==0:raise ArithmeticError('unprojected identically zero Phi')
 G=gcdp(ph,h4)
 if len(G)==1:return None
 ph,re=qr(ph,G);assert not re
 return [list(v.x) if isinstance(v,ExactV) else list(W(v).x) for v in ph]

def splits_h4(front,slot,M,flags):
 try:Y=allowed(front,slot,M,flags)
 except SplitAt as e:
  J0=mon(e.d)
  J1,rem=qr(M,J0);assert not rem
  return splits_h4(front,slot,J0,flags)+splits_h4(front,slot,J1,flags)
 return [(M,flags,Y)]

def mark_h4(front,slot,br,Z):
 if br!=0:return [(X,bs,None) for X,bs in Z]
 H=bad_diag(front,slot)
 Y=[]
 for X,flags in Z:
  D=gcdp(X,H)
  R=guarded(X,[H])
  if len(D)>1:Y+=splits_h4(front,slot,mon(D),flags)
  if len(R)>1:Y.append((mon(R),flags,None))
 print('exact H4 padding quotient',front,slot,[(len(D)-1,None if Y0 is None else len(Y0)-1) for D,_,Y0 in Y],flush=True)
 return Y
