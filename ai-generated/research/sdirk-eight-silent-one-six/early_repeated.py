"""One early silent zero and only the terminal repeat: exact five-site fibers."""
from equal_six import *
from off8_fibers import multicol

def raw(rear,e):
 A,B,_=ends(rear,e)
 D=(X-(1-Y))*(X-(1-Y*A))*(X-(1-Y*B))
 H=[JJ.from_dict({(j,):v for (i,j),v in avg(D,k).items() if not i}) for k in range(5)]
 a,b,c,d,z=H
 T=trip(H);P=a*c-b*b
 assert T and P
 guards=G*P
 while True:
  F=T.gcd(guards)
  if F.degree()==0:break
  T=T.exquo(F)
 T=T.exquo(T.gcd(T.diff(G))).monic()
 print('five-site fixed tail diagonal factors',rear,e,[(q.degree(),m) for q,m in T.factor_list()[1]],flush=True)
 return T,H

def reduced(front,rear,e,M,H,p,t):
 B0=Bfield(nmod_poly([0,1],p),p,t)
 Md=B0.cast(Epoly(M))
 assert Md.degree()==M.degree() and Md.leading_coefficient()==1
 for f,m in Md.factor()[1]:
  assert m==1
  U=Bfield(f,p,t)
  g=U(nmod_poly([0,1],p));x=1-g
  W=[U(Epoly(q)) for q in H]
  a,b,c,d,_=W;hh=a*c-b*b
  y=[(b*d-c*c)/hh/g**2,(b*c-a*d)/hh/g,U(1)]
  cv=lambda q:U(Epoly(JJ(q))) if q else U(0)
  A,B,r=map(cv,ends(front,1))
  ha,hb=(A-1)/2,(B-1-r)/2
  h0=[cv(x) for x in pol(h4(front),lambda v:v)]
  yield U,g,x,y,h0,A,B,r,ha,hb
def fifth_silent(front,rear,e,M,H,p,t):
 for U,g,x,y,h0,*_ in reduced(front,rear,e,M,H,p,t):
  ev(h0,x/g).inv()
  assert len(gcdp(h0,y))==1
 return True
