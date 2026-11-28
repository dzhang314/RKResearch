"""Check content and exact source guards for the finite lone-fourth transport gate."""
from nonliteral_fourth_projection import *
from shared_silent8_projection import red_e
from itertools import product

def cg(V):
 W=[m for m in V if m]
 assert W
 C=min(W,key=lambda p:p.degree()).monic()
 for p in W:
  if C.degree()==0:break
  C=egcd(C,p)
 return C

def gamma_of(W):
 V=E_su(W)
 assert len(V)==1 and len(V[0])==1
 return V[0][0]

def as_es(W):
 X={}
 for (j,k,b,c,d),v in W.to_dict().items():
  assert not (j or b or c)
  if k not in X:X[k]=[0,0]
  X[k][d]=v
 n=max(X,default=-1)
 return E(*[P([X.get(k,[0,0])[i] for k in range(n+1)]) for i in range(2)])

def contents(f,i):
 fd=frontdata(f,i)
 assert len(gcdp(fd[8],exact_uc_y(fd[19])))==1
 J,T,V,D,Q0,P0,gs=profiles(f,i)
 H=[w[0] for w in E_su(J) if w]
 a=C(frontdata(f,i)[5]);allowed=[gamma_of(g),gamma_of(L(g*a))]
 c=cg(H)
 assert eguard(c,allowed).degree()==0
 G=cg(map(as_es,coeff_var(D,0)))
 assert G.degree()==0
 print('exact j4 content and pointwise gap witness',f,i,c.degree(),G.degree(),flush=True)
 # R(u) cannot be identically zero at a genuine gamma,s: evaluate
 # its raw ninth cross at c=z, where only q(x)(x-z)L4(z) remains.
 return True

if __name__=='__main__':
 for f,i in product((True,False),(0,1)):
  assert contents(f,i)
 for f,i,r in product((True,False),(0,1),(True,False)):
  assert verify(f,i,r)
 print('true single nonliteral fourth finite clock/weight chart: 8')
