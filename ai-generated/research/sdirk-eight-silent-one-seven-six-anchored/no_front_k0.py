"""Both literal front stages silent, six distinct active clocks, k=0."""
from both_front_active8 import *
from equal_undetected_front import lagrange

def verify(front,zslot,rear,orient,p,t):
 U=Bfield(nmod_poly(list(Lco),p),p,t)
 R0=U(nmod_poly([0,1],p))
 cv=lambda x:U(Epoly(JJ(x))) if x else U(0)
 A,B,r=map(cv,ends(front,1));ha,hb=(A-1)/2,(B-1-r)/2
 X,g=(A if zslot==0 else B),1/(1+(A if zslot==0 else B))
 Xh=ha if zslot==0 else hb
 R=R0/g
 C,D,_=map(cv,ends(rear,orient));c,d=1/g-C,1/g-D
 L=[U(i)*g**j for j,i in enumerate(Lco)]
 P,rem=qr(L,[-R,U(1)]);assert not rem and len(P)==4
 P=sc(P,Xh/ev(P,X))
 H4=[cv(v) for v in pol(h4(front),lambda z:z)]
 pegs=[g*v for v in (X,c,d,R)]
 D=nodal(pegs);M=[intp(U,D,j) for j in range(4)]
 a,b,cc,dd=M;hh=a*cc-b*b
 Y=[(b*dd-cc*cc)/(hh*g*g),(b*cc-a*dd)/(hh*g),U(1)]
 multicol(Y,add(H4,sc(P,-1))).inv()
 h=ev(H4,R)
 h.inv()
 ta=(B*(R-1-2*h)-(R*R/2-R-2*h))/(B-A);tb=R-1-2*h-ta
 TR=R**3-R**4/4+2*h+ta*A**3+tb*B**3
 AR=h+ta*ha+tb*hb
 TX=(A**3+A-1-A**4/4) if zslot==0 else (B**3+B-1-r+r*A**3-B**4/4)
 AX=ha if zslot==0 else hb+r*ha
 def line(zv,xv):
  m=(zv/h-xv/Xh)/(R-X)
  return [xv/Xh-X*m,m]
 QT,QA=line(TR,TX),line(AR,AX)
 ns=[A,B,R];hp=[ha,hb,h]
 cards=lagrange(ns)
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
