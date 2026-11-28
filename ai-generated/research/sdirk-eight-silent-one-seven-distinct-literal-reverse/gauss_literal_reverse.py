"""Gauss-hole reverse root at an actual silent literal front."""
from literal_terminal import *
from one_front_zero import Pcoeff
from variable_gamma import Lf,G as Gamma

def data(f,i):
 F=ExField(Epoly(Lf(Gamma).monic()))
 A,B,m=map(lambda x:cv(F,x),ends(f,1));b=(A,B)[i]
 r=F(E(P([0,1])));g=r/b;x=1-g
 (x-r).inv()
 Qp=Pcoeff(F,r)
 assert len(Qp)==4
 u=[F(0),F(1)];k=[F(1),F(2),F(-1)]
 c=[x,-g]
 px=ev(Qp,x);pc=subst(Qp,c)
 px.inv();g.inv()
 C=add(sc(pc,x-r),sc(mul(k,[x-r,-g]),-px))
 assert C[0]==0
 C=C[1:]
 return F,r,g,x,Qp,k,px,C

def verify(f,i,kind):
 F,r,g,x,Qp,k,px,C=data(f,i)
 u=[F(0),F(1)];c=[x,-g]
 v=(x-r)/g
 if kind is None:
  # Physical eight has nonzero reverse weight; it must share the root r.
  T=add([2*(x-r)],sc(mul(k,[F(-2),F(1)]),g))
  G=gcdp(C,T)
  assert len(G)==1
  ev(T,v).inv()
 else:
  d=[x-2*g,g] if kind else [x,-2*g]
  pd=subst(Qp,d)
  if kind:
   D=add(sc(pd,x-r),sc(mul(k,add(d,[-r])),-px))
  else:
   H=[F(-2),F(1),F(4),F(-1)]
   B=[F(2),F(3),F(-12),F(4)]
   D=add(sc(mul(H,pd),x-r),sc(mul(mul(k,B),add(d,[-r])),px))
  v2=2-v if kind else v/2
  assert len(gcdp(C,D))==1
  ev(D,v).inv();ev(C,v2).inv()
 print('verified exact Gauss literal reverse root:',f,i,kind,flush=True)
 return True
