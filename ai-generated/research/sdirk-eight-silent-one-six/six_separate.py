"""Virtual seventh pure-profile site with physically silent row eight."""
from seven_distinct import *
def check_separate(front,p,t):
 for V,g,x,s,y,z in third(front,p,t):
  P4=nodal([s,y,z,x])
  A=[sum(V(v)/(i+j+1) for i,v in enumerate(P4)) for j in range(4)]
  P3=nodal([s,y,z])
  B=[sum(V(v)/(i+j+1) for i,v in enumerate(P3)) for j in range(5)]
  C=[x,-g]
  D=[x-g,-3*g/2,2*g,-g/2]
  marked=lambda m,i,e:add([m[i]],sc(e,-m[i-1]))
  def W(e):
   Q1,Q2,Q3=[marked(A,i,e) for i in (1,2,3)]
   return add(mul(Q2,Q2),sc(mul(Q1,Q3),-1))
  Wc,Wd=W(D),W(C)
  cd=mul(C,D);su=add(C,D)
  N=[add(add([B[i+2]],sc(su,-B[i+1])),sc(cd,B[i])) for i in range(3)]
  Wx=add(mul(N[1],N[1]),sc(mul(N[0],N[2]),-1))
  k=[V(1),V(2),-V(1)]
  F9=add(mul(k,Wc),sc(Wx,-1))
  assert F9[0]==0
  assert len(Wd)==3
  G=monic_u(Wd)
  multicol(G,F9[1:]).inv()
 return True
