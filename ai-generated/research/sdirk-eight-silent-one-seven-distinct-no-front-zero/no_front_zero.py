"""Zero-factor seven-distinct with neither literal front active."""
from literal_terminal import *

def coords(F,f,slot,rear,ori):
 A,B,m=map(lambda q:cv(F,q),ends(f,1));a,b,v=map(lambda q:cv(F,q),ends(rear,ori))
 ha,hb=(A-1)/2,(B-1-m)/2
 X,hh=(A,ha) if slot==0 else (B,hb)
 g=1/(1+X);C=1/g-a;D=1/g-b
 L=[F(k)*g**j for j,k in enumerate(Lco)]
 nu=(a-1)*ev(L,D);mu=-(b-1-v)*ev(L,C)
 qa=ev(L,X)/hh
 q1=-qa*(nu+mu)/(nu*(C-X)+mu*(D-X));q0=qa-X*q1
 H4=[cv(F,q) for q in pol(h4(f),lambda v:v)]
 return A,B,m,ha,hb,X,g,C,D,q0,q1,L,H4

@lru_cache(None)
def diag(f,slot,rear,ori):
 F=F2
 A,B,m,ha,hb,X,g,C,D,q0,q1,L,H4=coords(F,f,slot,rear,ori)
 E=add(mul([q0,q1],H4),sc(L,-1))
 J=list(map(F,nodal([A,B,C,D])))
 S=mon(guarded(E,[J]))
 print('no active literal front zero factor',f,slot,rear,ori,len(S)-1,bool(q1),flush=True)
 return S,bool(q1)

def verify(f,slot,rear,ori,p,t):
 G,qtype=diag(f,slot,rear,ori)
 if len(G)<=1:return True
 B=Bfield(nmod_poly([0,1],p),p,t)
 Md=nmod_poly([int(B(x).x[0]) for x in G],p)
 assert Md.degree()==len(G)-1 and Md.leading_coefficient()==1
 for M,_ in Md.factor()[1]:
  U=Bfield(M,p,t);s=U(nmod_poly([0,1],p))
  A,B,m,ha,hb,X,g,C,D,q0,q1,L,H4=coords(U,f,slot,rear,ori)
  assert bool(q1)==qtype
  Y=missing(U,g,q0,q1,[g*x for x in (X,C,D,s)],3)
  assert Y is not None
  testrow5(U,f,slot,A,B,m,ha,hb,X,g,X,C,D,q0,q1,L,H4,s,Y,False)
 return True
