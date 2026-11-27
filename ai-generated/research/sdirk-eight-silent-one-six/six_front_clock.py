"""Late physically silent zero clock equal to a or b, with six active."""
from seven_distinct import *
def scaled(V,pegs):
 P=nodal_u(pegs)
 m0,m1=integrate(V,P),integrate(V,P,1)
 def W(j):
  D=nodal_u(pegs[:j]+pegs[j+1:])
  return add(mul(m0,integrate(V,D,1)),sc(mul(m1,integrate(V,D)),-1))
 return W

def fixed(V,pegs):
 P=nodal_u(pegs)
 return integrate(V,P), lambda j:integrate(V,nodal_u(pegs[:j]+pegs[j+1:]))
def tail(V,g,x,back):
 U=[V(0),V(1)]
 c=[x,-g]
 d=[x-2*g,g] if back else [x,-2*g]
 k=[V(1),V(2),-V(1)]
 return U,c,d,k
def z6(front,back,flag,p,t):
 for U,a,b,s,y,ha,hb,Ah,AhY,T4,Q in projection_data(front,p,t):
  V=Nested(Q);g=V.gen()
  s,y,a,b=[V(j)*g for j in (s,y,a,b)]
  x=1-g;f=a if flag else b
  u,c,d,k=tail(V,g,x,back)
  W=scaled(V,[[v] for v in (s,y,f,x)]+[c,d])
  F9=add(mul(k,W(4)),sc(W(3),-1))
  assert len(F9)==5 and F9[0]==0
  mon=monic_u(F9[1:])
  multicol(mon,W(2)).inv()
 return True

def abcv(V,front,use_a):
 A,B,_=ends(front,1)
 return V(Epoly(JJ(A if use_a else B)))

def z7(front,back,flag,p,t):
 for V,g,x,s,y,z in third(front,p,t):
  f=g*abcv(V,front,flag)
  u,c,d,k=tail(V,g,x,back)
  I,W=fixed(V,[[v] for v in (s,y,z,f,x)]+[c,d])
  assert len(I)==3
  mon=monic_u(I)
  multicol(mon,W(3)).inv()
 return True
def z8(front,flag,p,t):
 for V,g,x,s,y,z in third(front,p,t):
  f=g*abcv(V,front,flag)
  u,c,d,k=tail(V,g,x,True)
  W=scaled(V,[[v] for v in (s,y,z,f,x)]+[c])
  S=add([2*(f-x)],sc(mul(k,[V(-2),V(1)]),-g))
  assert len(S)==4
  mon=monic_u(S)
  multicol(mon,W(3)).inv()
 return True
