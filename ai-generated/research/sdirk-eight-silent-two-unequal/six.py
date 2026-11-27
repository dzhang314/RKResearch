"""Six active zeros with unequal invisible residuals."""
from unequal_finite import *

def six(front,model=None):
 M,F,q=model or exact_fifth(front)
 g=q[0]
 u=[F(0),F(1)]
 c=[g,g] # reflected penultimate clock
 L=sum_poly([sc(power(c,i),F(x)) for i,x in enumerate(Lco)])
 k=[F(1),F(2),F(-1)];d=[F(-2),F(1),F(4),F(-1)]
 qs=add(mul([F(1),F(4),F(-4)],d),[F(0),F(0),F(-8),F(12)])
 d8=add(sc(u,2),mul(k,[F(-2),F(1)]))
 for a in (k,qs,d8):
  assert len(gcdp(a,L))==1
 print("six-active cases excluded",front,flush=True)
if __name__=='__main__':
 for f in (True,False):six(f)
