"""Both active literal fronts and six distinct active clocks with k=0."""
from both_front_silent8 import *

def verify_active(front,M,rear,orient,p,t):
 F0,g,X,R,A,B,r,ha,hb,P,Q,C,H4=model(front,M)
 cv=lambda r:F0(Epoly(JJ(r))) if r else F0(0)
 AA,BB,_=map(cv,ends(rear,orient))
 c,d=X+1-AA,X+1-BB
 d0=(g,X,R,A,B,r,ha,hb,P,Q,C,H4,c,d)
 count=int(R==A)+int(R==B)+int(R==c)+int(R==d)
 assert count<=2
 for U,u in reduced(M,p,t,[F0(0),F0(1)]):
  g,X,R,A,B,r,ha,hb=map(U,d0[:8]);P,Q,C,H4=[list(map(U,f)) for f in d0[8:12]]
  c,d=map(U,d0[12:])
  pegs=[A,B,X,c,d]
  if count==0:pegs.append(R)
  if count==2:
   inds=[i for i,v in enumerate([d0[3],d0[4],d0[1],d0[12],d0[13]]) if v==d0[2]]
   pegs.pop(inds[0])
  D=nodal([g*z for z in pegs]);J=lambda j:intp(U,D,j)
  if count==0:
   try:J(0).inv()
   except ArithmeticError:J(1).inv()
  elif count==1:
   (J(0)*J(2)-J(1)*J(1)).inv()
  else:
   Y=reconstruct(U,g,pegs)
   E=first5(U,A,B,r,ha,hb,C,H4)
   ev(E,X).inv();multicol(Y,E).inv()
 return True

def verify_silent(front,M,orient,p,t):
 F,g,X,R,A,B,r,ha,hb,P,Q,C,H4=model(front,M)
 AA=F(Epoly(JJ(ends(True,orient)[0])))
 u=AA-1;c=X-u
 return verify(front,M,c==R,p,t,gap=u)
