"""Independent six-clock with the active literal front itself the Gauss double."""
from both_front_silent8 import *
from front_root import verify as direct

def silent8(f,M,p,t):
 F,g,X,R,A,B,m,ha,hb,P,Q,C,H4=model(f,M)
 if A==R:Z=B
 elif B==R:Z=A
 else:return True
 for rn in (False,True):
  if rn:
   u=X-R
   k=1+2*u-u*u
   need=X+k*(u-2)/2-Z
   assert need
   W=[-u,F(1)]
  else:W=tail_projection(f,M,False)
  d0=(X,Z)
  for U,u in reduced(M,p,t,W):
   XX,ZZ=map(U,d0);k=1+2*u-u*u
   (XX+k*(u-2)/2-ZZ).inv()
 return True
