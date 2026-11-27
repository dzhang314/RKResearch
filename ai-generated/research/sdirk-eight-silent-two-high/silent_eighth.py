"""Additional literal split when the second invisible stage is physical eight."""
from midpoint import *
from off8_fibers import cramer

def twofront():
 for f,i in product((True,False),(0,1)):
  a,b,_=ends(f,1);A,B=(a,b) if i==0 else (b,a)
  g=K.one/(1+A);x=1-g;u=A-B;k=1+2*u-u*u
  gate=2*(g-x)-g*k*(u-2)
  print('nonhalf silent tail',f,i,K.to_sympy(gate))
  assert gate

def half(front):
 F=ExField(Epoly(G-K.one/2));g=F(1)/2;x=g
 cv=lambda t:F(Epoly(JJ(t))) if t else F(0)
 A,B,r=ends(front,1)
 a,b=g*cv(A),g*cv(B)
 ha,hb=g**3*cv((A-1)/2),g**3*cv((B-1-r)/2)
 L=list(map(F,Lco))
 d=(ev(L,b)/hb-ev(L,a)/ha)/(b-a)
 Q=[ev(L,a)/ha-a*d,d]
 assert d and len(gcdp(Q,L))==1
 hh=[g**(3-j)*cv(v) for j,v in enumerate(pol(h4(front),lambda c:c))]
 G4=add(mul(Q,hh),sc(L,-1))
 assert ev(G4,g) # row four cannot be one of the two midpoint copies
 for sign in (1,-1):
  U=ends(True,sign)[0];c=1-g*cv(U)
  pegs=[a,b,x,c]
  assert all(a!=b for a,b in combinations(pegs,2))
  M=moment(F,pegs,Q,6)
  H=[[M[i+j] for j in range(3)] for i in range(3)]
  v=det(H)
  if not v:
   print('half silent tail zero cubic pivot excludes',front,sign)
   raise AssertionError('expected all four signed pivots to be nonzero')
  P=[s/v for s in cramer(H,[-M[i+3] for i in range(3)])]+[F(1)]
  G0=gcdp(P,G4)
  print('half silent tail reconstructed gate gcd degree',front,sign,len(G0)-1)
  assert len(G0)==1
if __name__=='__main__':
 twofront()
 for f in (True,False):half(f)
