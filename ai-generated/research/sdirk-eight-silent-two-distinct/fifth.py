"""Literal nth active rank monitor, normalized actual rows 2--5."""
from nodal import *
def tau(z,t,a,b):
 return z**3+sum(v*q**3 for v,q in zip(t,[1,a,b]))-z**4/4

def fifth(data,N):
 g,x,c,d,a,b,s,ha,hb,rr,lam,q,h4p=data
 U=g.A
 hs=ev(h4p,s)
 ta=(b*(s-1-2*hs)-(s*s/2-s-2*hs))/(b-a)
 tb=(s*s/2-s-2*hs-a*(s-1-2*hs))/(b-a)
 FF=[
  [ha,a*ha,ha,tau(a,[a-1],a,b)],
  [hb,b*hb,hb+rr*ha,tau(b,[b-1-rr,rr],a,b)],
  [hs,s*hs,hs+ta*ha+tb*hb,tau(s,[2*hs,ta,tb],a,b)]]
 cof=[(-1)**(3+j)*det([[r[i] for i in range(4) if i!=j] for r in FF]) for j in range(4)]
 cards=lagrange([a,b,s])
 def relation(h):
  M=[[-U(1)-2*h,U(1)],[-2*h,-U(1),U(1)/2],[-4*h/3,U(0),-U(1),U(1)/3]]
  ws=[sum_poly([sc(m,d) for m,d in zip(M,d0)]) for d0 in cards]
  Ah=add([h],sum_poly([sc(w,v) for w,v in zip(ws,[ha,hb,hs])]))
  T4=add([2*h,U(0),U(0),U(1),-U(1)/4],sum_poly([sc(w,v**3) for w,v in zip(ws,[a,b,s])]))
  return sum_poly([sc(z,v) for z,v in zip([[h],[U(0),h],Ah,T4],cof)])
 R0=relation(U(0));R1=add(relation(U(1)),sc(R0,-1))
 Q=[q[0],q[1]*g]
 C=physical_L([U(0),g])
 F5=add(mul(Q,R0),sc(mul(C,R1),lam))
 H=[N[i]*g**i for i in range(len(N))];H=sc(H,H[-1].inv())
 out=multicol(H,F5)
 return out,H,F5,R0,R1
