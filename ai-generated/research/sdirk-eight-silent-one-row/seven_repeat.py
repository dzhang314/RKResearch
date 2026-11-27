"""One invisible donor, seven active zeros, undetected h and a repeat."""
from equal_undetected_front import *
from equal_detected import ends
def check_seven(front,rear,sg,p,t):
 for U,a,b,s,y,ha,hb,Ah,AhY,T4,Q in projection_data(front,p,t):
  W=Nested(Q);g=W.gen();s,y=map(W,(s,y))
  A,B,_=ends(rear,sg)
  B0=U.B
  cv=lambda e:W(U(B0(Epoly(JJ(e))))) if e else W(0)
  x=1-g;c,d=1-g*cv(A),1-g*cv(B)
  P=nodal([g*s,g*y,x,c,d]);I=lambda w,j:sum(W(c)/(i+j+1) for i,c in enumerate(w))
  m0,m1,m2=[I(P,j) for j in range(3)]
  (m0*m2-m1*m1).inv()
 return True
