"""Exactly one literal front active, k=0, x=r and eighth silent."""
from both_front_active8 import *
from equal_undetected_front import lagrange
def model0(front,zi,p,t):
 J0=nmod_poly(list(Lco),p)
 for J,e in J0.factor()[1]:
  assert e==1
  U=Bfield(J,p,t);R0=U(nmod_poly([0,1],p))
  cv=lambda x:U(Epoly(JJ(x))) if x else U(0)
  A,B,r=map(cv,ends(front,1));ha,hb=(A-1)/2,(B-1-r)/2
  anc,ah=(B,hb) if zi==0 else (A,ha)
  g=1-R0;R=R0/g
  L=[U(i)*g**j for j,i in enumerate(Lco)]
  P,er=qr(L,[-R,U(1)]);assert not er and len(P)==4
  P=sc(P,ah/ev(P,anc))
  H4=[cv(v) for v in pol(h4(front),lambda z:z)]
  yield U,(A,B,r,ha,hb,anc,ah,R),P,H4
def clean_pair(U,data,P,H4,y0,hs):
 A,B,r,ha,hb,anc,ah,R=data
 ta=(B*(y0-1-2*hs)-(y0*y0/2-y0-2*hs))/(B-A);tb=y0-1-2*hs-ta
 T4=y0**3-y0**4/4+2*hs+ta*A**3+tb*B**3
 A4=hs+ta*ha+tb*hb
 Tf=A**3+A-1-A**4/4 if anc==A else B**3+B-1-r+r*A**3-B**4/4
 Af=ha if anc==A else hb+r*ha
 def L(z,v):
  B1=(z/hs-v/ah)/(y0-anc);return [v/ah-anc*B1,B1]
 QT,QA=L(T4,Tf),L(A4,Af)
 ps=[A,B,y0];hp=[ha,hb,hs]
 cards=lagrange(ps)
 def gates(H):
  m0=add([U(-1),U(1)],sc(H,-2))
  m1=add([U(0),U(-1),U(1)/2],sc(H,-2))
  m2=add([U(0),U(0),U(-1),U(1)/3],sc(H,-U(4)/3))
  w=[sum_poly([sc(q,v) for q,v in zip([m0,m1,m2],p0)]) for p0 in cards]
  F1=sum_poly([[U(0),U(0),U(0),U(1),-U(1)/4],sc(H,2),sc(mul(QT,H),-1),*[sc(v,d**3) for v,d in zip(w,ps)]])
  F2=sum_poly([H,sc(mul(QA,H),-1),*[sc(v,d) for v,d in zip(w,hp)]])
  return F1,F2
 return gates
def trim_guard(F,G,n,U):
 P,r=qr(F,nodal(G));assert not r and len(P)==n+1
 return P
def verify(front,zi,p,t):
 for U,data,P,H4 in model0(front,zi,p,t):
  A,B,r,ha,hb,anc,ah,R=data
  # row4 is the other r occupant: row5 singleton.
  gates=clean_pair(U,data,P,H4,R,ev(H4,R))
  F,G=gates(P)
  F=trim_guard(F,[anc],3,U)
  G,rem=qr(G,nodal([anc]));assert not rem
  multicol(mon(F),G).inv()
  # row4 singleton: first polynomial has the exact earlier active clock factor.
  J=trim_guard(add(H4,sc(P,-1)),[anc],2,U)
  T=Tower(mon(J));z=T.gen()
  D=list(map(T,data));P0,H0=list(map(T,P)),list(map(T,H4));hs=ev(H0,z)
  gates=clean_pair(T,D,P0,H0,z,hs)
  F,G=gates(P0)
  F=trim_guard(F,[D[5],z],2,T)
  G,r2=qr(G,nodal([D[5],z]));assert not r2
  multicol(mon(F),G).inv()
  # row5 is the other actual r occupant, not assigned the cubic value there.
  af,bf=gates([T(0)]);cf,df=gates([T(1)])
  q0,q1,q2,q3=[ev(U0,D[-1]) for U0 in (af,bf,cf,df)]
  (q0*q3-q1*q2).inv()
 return True
