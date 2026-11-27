"""Dependent cubic-defect double: finite active-eighth three-peg tests."""
from one_front_zero import *
from equal_detected import det3

def check(front,slot,rear,hit,mode,orient,p,t):
 assert mode or orient in (1,-1)
 m=[2,3,-12,4] if mode else [0,1]
 base=Bfield(nmod_poly(m,p),p,t)
 cv=lambda a:base(Epoly(JJ(a))) if a else base(0)
 A,B,_=map(cv,ends(front,1))
 anc=A if slot==0 else B
 u=base(nmod_poly([0,1],p)) if mode else cv(ends(rear,orient)[0])-1
 G=1/(1+anc+(u if hit==9 else 0))
 x=1-G;c=x-G*u;d=x-G*(2-u if rear else 2*u)
 hg=pol(h4(front).monic(),cv);S=Tower(list(hg));s=S.gen()
 G,x,c,d=map(S,(G,x,c,d))
 other=c if hit==10 else x
 if mode or hit==9:ev(list(map(S,hg)),other/G).inv()
 q=nodal([other,d,G*s])
 ms=[intp(S,q,j) for j in range(5)]
 det3(ms).inv()
 return True
