"""Exact rear Gauss ratio and five-site Hankel tests."""
import sympy as S
from sympy.polys.rings import ring
from itertools import product
K=S.QQ.algebraic_field(S.sqrt(2)/2)
J,X=ring("X",K)
t=K.unit
L4=lambda X:70*X**4-140*X**3+90*X*X-20*X+1
def ends(star,s):
 return 2+2*s*t, 2-2*s*t if star else 3+4*s*t
def avg(p):
 return sum(v/(j+1) for (j,),v in p.items())
def det3(x):
 return x[0]*x[2]*x[4]+2*x[1]*x[2]*x[3]-x[0]*x[3]**2-x[1]**2*x[4]-x[2]**3
def run():
 for star,s in product((True,False),(1,-1)):
  A,B=ends(star,s)
  assert L4(A*X).gcd(L4(B*X)).degree()==0
  print('rear Gauss pair excluded',star,s,flush=True)
 for front,j,back,p in product((True,False),(0,1),(True,False),(1,-1)):
  gamma=K.one/(1+ends(front,1)[j])
  assert L4(gamma) # terminal clock literally equals a front zero
  A,B=ends(back,p)
  c=1-gamma;c9=1-gamma*A;c8=1-gamma*B
  assert len(set((c,c9,c8)))==3
  P=(X-c)*(X-c9)*(X-c8)
  value=det3([avg(P*X**j) for j in range(5)])
  if value:
   print('five-site determinant nonzero',front,j,back,p,flush=True)
   continue
  A0,A1,A2,A3=[avg(P*X**i) for i in range(4)]
  den=A0*A2-A1*A1
  if not den:
   print('five-site Hankel rank after guard fails',front,j,back,p,flush=True)
   continue
  V=(A1*A3-A2*A2)/den
  U=(A1*A2-A0*A3)/den
  QQ=X*X+U*X+V
  aa,bb=[gamma*w for w in ends(front,1)]
  G=(X-gamma)*(X-aa)*(X-bb)
  T=sum(co*X**(i+1)/(i+1) for (i,),co in G.items())-gamma*G
  gg=QQ.gcd(T)
  print('five-site residual exact gcd',front,j,back,p,gg.degree(),flush=True)
  assert gg.degree()==0
if __name__=='__main__':run()
