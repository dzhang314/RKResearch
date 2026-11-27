"""Six active zeros, undetected h, late third silent with attached reverse clock."""
from seven_distinct import *
def test(front,sign,p,t):
 for V,g,x,s,y,z in third(front,p,t):
  a,b,_=ends(True,sign)
  def cv(e):return V(Epoly(JJ(e))) if e else V(0)
  c=1-g*cv(a)
  P=nodal([s,y,z,x,c])
  I=lambda j:sum(V(v)/(i+j+1) for i,v in enumerate(P))
  A,B,C=[I(j) for j in range(3)]
  (A*C-B*B).inv()
 return True
