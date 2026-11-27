"""Two finite-anchor subcases with exactly one literal front active at k=0."""
from both_front_active8 import *
from equal_undetected_front import lagrange

def verify(front,zi,rear,orient,terminal_is_gauss,p,t):
 U=Bfield(nmod_poly(list(Lco),p),p,t)
 R0=U(nmod_poly([0,1],p))
 cv=lambda x:U(Epoly(JJ(x))) if x else U(0)
 A,B,r=map(cv,ends(front,1));ha,hb=(A-1)/2,(B-1-r)/2
 # zi chooses the actual silent literal front, the other anchor is active.
 sil,anc=(A,B) if zi==0 else (B,A)
 ah=hb if zi==0 else ha
 g=1-R0 if terminal_is_gauss else 1/(1+sil)
 X=1/g-1;R=R0/g
 AA,BB,_=map(cv,ends(True if rear is None else rear,orient))
 C,D=X+1-AA,X+1-BB
 L=[U(i)*g**j for j,i in enumerate(Lco)]
 P,er=qr(L,[-R,U(1)]);assert not er
 P=sc(P,ah/ev(P,anc))
 if not terminal_is_gauss and rear is not None:
  pegs=[g*z for z in (anc,X,C,D,R)]
  D0=nodal(pegs);J=lambda j:intp(U,D0,j)
  (J(0)*J(2)-J(1)**2).inv()
  return True
 assert rear is not None or not terminal_is_gauss
 H4=[cv(v) for v in pol(h4(front),lambda z:z)]
 pegs=[anc,X,C,D] if terminal_is_gauss else [anc,X,C,R]
 D=nodal([g*z for z in pegs]);J=lambda j:intp(U,D,j)
 a,b,cc,dd=[J(j) for j in range(4)];hh=a*cc-b*b
 Y=[(b*dd-cc*cc)/(hh*g*g),(b*cc-a*dd)/(hh*g),U(1)]
 multicol(Y,add(H4,sc(P,-1))).inv()
 h=ev(H4,R);h.inv()
 ta=(B*(R-1-2*h)-(R*R/2-R-2*h))/(B-A);tb=R-1-2*h-ta
 TR=R**3-R**4/4+2*h+ta*A**3+tb*B**3
 AR=h+ta*ha+tb*hb
 TF=(B**3+B-1-r+r*A**3-B**4/4) if zi==0 else (A**3+A-1-A**4/4)
 AF=hb+r*ha if zi==0 else ha
 def line(zv,xv):
  m=(zv/h-xv/ah)/(R-anc)
  return [xv/ah-anc*m,m]
 QT,QA=line(TR,TF),line(AR,AF)
 ns=[A,B,R];hp=[ha,hb,h];cards=lagrange(ns)
 m0=add([U(-1),U(1)],sc(P,-2))
 m1=add([U(0),U(-1),U(1)/2],sc(P,-2))
 m2=add([U(0),U(0),U(-1),U(1)/3],sc(P,-U(4)/3))
 w=[sum_poly([sc(q,v) for q,v in zip([m0,m1,m2],p0)]) for p0 in cards]
 F1=sum_poly([[U(0),U(0),U(0),U(1),-U(1)/4],sc(P,2),sc(mul(QT,P),-1),
              *[sc(v,d**3) for v,d in zip(w,ns)]])
 F2=sum_poly([P,sc(mul(QA,P),-1),*[sc(v,d) for v,d in zip(w,hp)]])
 try:multicol(Y,F1).inv()
 except ArithmeticError:multicol(Y,F2).inv()
 mm=[U(-2),U(-2),-U(4)/3]
 dt=[sum(v*z for v,z in zip(L0,mm)) for L0 in cards]
 Tap=2+sum(v*z**3 for v,z in zip(dt,ns))-ev(QT,R)
 Aap=1+sum(v*z for v,z in zip(dt,hp))-ev(QA,R)
 try:Tap.inv()
 except ArithmeticError:Aap.inv()
 return True
