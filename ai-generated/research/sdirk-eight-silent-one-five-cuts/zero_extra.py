"""Five ordinary active sites, both extra silent cubic defects zero."""
from seven_distinct import third,tests
from six_separate import check_separate
from equal_undetected_front import *
from equal_detected import ends

def minor(V,pegs):
 Q=nodal(pegs)
 a,b,c=[sum(V(v)/(i+j+1) for i,v in enumerate(Q)) for j in range(3)]
 return a*c-b*b

def const(V,v):return V(Epoly(JJ(v))) if v else V(0)

def repeated(front,p,t):
 for U,a,b,s,y,ha,hb,Ah,AhY,T4,Q in projection_data(front,p,t):
  W=Nested(Q);g=W.gen();x=1-g
  prefs=[W(s)*g,W(y)*g]
  for choice in (0,1):
   silent,active0=prefs[choice],prefs[1-choice]
   # Nonzero reverse factor and a silent eighth forces the earlier silent clock to be c9=x−2γ.
   (silent-(x-2*g)).inv()
   for rear in (True,False):
    # Nonzero reverse factor, active eighth: c9 is pinned at the early silent clock.
    u=(x-silent)/g;c9=silent;c8=x-g*(2-u if rear else 2*u)
    minor(W,[x,c9,c8,active0]).inv()
    # Zero reverse factor, active eighth.
    for e in (1,-1):
     A,B,_=ends(rear,e)
     c9,c8=1-g*const(W,A),1-g*const(W,B)
     minor(W,[x,c9,c8,active0]).inv()
 return True
def silent_k0(front,p,t):
 for V,g,x,s,y,z in third(front,p,t):
  for e in (1,-1):
   A=ends(True,e)[0];c9=1-g*const(V,A)
   for act in (s,y):
    minor(V,[x,c9,z,act]).inv()
 return True
