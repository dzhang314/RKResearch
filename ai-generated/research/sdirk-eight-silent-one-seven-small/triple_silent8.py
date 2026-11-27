"""Detected seven-active ordinary triple, k!=0 and literal eighth silent."""
from equal_undetected_front import *
from equal_detected import h4,ends
def ccv(B,x):return B(Epoly(JJ(x))) if x else B(0)

def both_low(front,pos,w,p,t,gap):
 for U,a,b,s,y,ha,hb,Ah,AhY,T4,Q in projection_data(front,p,t):
  R=a if w==0 else b
  g=1/(1+R+(gap if pos==9 else 0))
  ev(Q,g).inv()
 return True

def early_triple(front,pos,w,p,t,gap):
 N=lambda x:nmod_poly(x,p)
 B0=Bfield(N([0,1]),p,t);h4p=B0.cast(Epoly(h4(front).monic()))
 for M,m in h4p.factor()[1]:
  U=Bfield(M,p,t);z=U(N([0,1]))
  A,B,rr=ends(front,1)
  a,b,r=map(lambda c:ccv(U,c),(A,B,rr))
  ha,hb=(a-1)/2,(b-1-r)/2
  s0=a if w==0 else b;hf=ha if w==0 else hb
  g=1/(1+s0+(gap if pos==9 else 0))
  ns=[a,b,z]
  tA=(b*(z-1)-(z*z/2-z))/(b-a)
  tB=z-1-tA
  Ah4=tA*ha+tB*hb
  T4=z**3-z**4/4+tA*a**3+tB*b**3
  L=lambda y:sum(U(v)*(g*y)**i for i,v in enumerate(Lco))
  betaA,betaT=Ah4/L(z),T4/L(z)
  tau_a=a**3+(a-1)-a**4/4
  tau_b=b**3+(b-1-r)+r*a**3-b**4/4
  Ah_a,Ah_b=ha,hb+r*ha
  TF=tau_a if w==0 else tau_b;AF=Ah_a if w==0 else Ah_b
  alphaA=(AF-betaA*L(s0))/hf
  alphaT=(TF-betaT*L(s0))/hf
  C=lagrange(ns)
  ds=[U(-2),U(-2),-U(4)/3]
  dt=[sum(a*b for a,b in zip(u,ds)) for u in C]
  dTau=2+sum(v*p**3 for v,p in zip(dt,ns))
  dAh=1+dt[0]*ha+dt[1]*hb
  assert (dTau-alphaT) or (dAh-alphaA)
 return True
