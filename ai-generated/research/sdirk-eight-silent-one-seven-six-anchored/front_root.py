"""Sole reverse-extra silent clock is one literal front; other front active."""
from both_front_active8 import *

def verify(f,M,rear,which,zi,p,t):
 F,g,X,R,A,B,m,ha,hb,P,Q,C,H4=model(f,M)
 Z=(A,B)[zi]
 if Z==R:return True # exact separate-clock restriction
 u,k,c,d,H,q3,A9,B9,A8,B8=tail_poly(F,X,R,C,rear)
 if not which:
  W=projection(f,M,rear)
  if len(W)==1:return True
 else:W=[-fixed_tail(F,X,R,rear,which),F(1)]
 eq9=add(B9,sc(A9,-Z))
 eq8=add(B8,sc(A8,-Z))
 EE=eq8 if which==9 else eq9
 for U,u in reduced(M,p,t,W):
  ev(list(map(U,EE)),u).inv()
 return True
