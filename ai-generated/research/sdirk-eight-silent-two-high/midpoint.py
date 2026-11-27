"""Exact half-diagonal Gauss and five-peg inverse moment gates."""
from equal_detected import h4,ends,Z
from unequal_finite import *
from variable_gamma import Lf

def midpoint(front):
 N=G-K.one/2
 F=ExField(Epoly(N));G0=F(1)/2;x=G0;g=G0
 cv=lambda t:F(Epoly(JJ(t))) if t else F(0)
 A,B,R=ends(front,1)
 a,b=map(cv,(A,B));a,b=a*g,b*g
 ha,hb=map(cv,((A-1)/2,(B-1-R)/2));ha,hb=ha*g**3,hb*g**3
 L=list(map(F,Lco))
 La,Lb=ev(L,a),ev(L,b)
 assert La and Lb and ev(L,g)
 X0=La/ha
 X1=Lb/hb
 u=(X1-X0)/(b-a);Q=[X0-a*u,u]
 assert u and len(gcdp(Q,L))==1
 # Degree-3 Gauss cardinal at a discrepancy r must share a and b
 # with the literal h values. Its only possible r is the same pole.
 C=add(sc([-b,F(1)],La*hb),sc([-a,F(1)],-Lb*ha))
 # Equivalently Q(r)=0 (check coefficients up to the known constant).
 assert C and len(gcdp(C,L))==1
 for st,t0 in product((True,False),(1,-1)):
  U,V,_=ends(st,t0)
  c,d=1-g*cv(U),1-g*cv(V)
  assert ev(L,c)
  pegs=[a,b,x,c,d]
  assert all(u!=v for u,v in combinations(pegs,2))
  assert det3(moment(F,pegs,Q))
 print('midpoint exact quadratic field: all four five-peg Hankels are nonzero',front,flush=True)
if __name__=='__main__':
 for front in (True,False):midpoint(front)
