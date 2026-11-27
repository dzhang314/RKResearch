"""One invisible donor, seven active distinct clocks, undetected h."""
from equal_undetected_front import *
from equal_detected import ends
from off8_fibers import multicol

def third(front,p,t):
 for U,a,b,s,y,ha,hb,Ah,AhY,T4,Q in projection_data(front,p,t):
  G=Nested(Q);g=G.gen(); g.inv()
  a,b,s,y,ha,hb,Ah,AhY,T4=map(G,(a,b,s,y,ha,hb,Ah,AhY,T4))
  ff=[a,b,s,y]
  baseL=[G(v)*g**j for j,v in enumerate(Lco)]
  Ls=ev(baseL,s);alpha,beta=Ah/Ls,T4/Ls
  raw,L=graph(ff,g,alpha,beta)
  cards=lagrange(ff)
  w=[sum_poly([sc(m,c) for m,c in zip(raw,v)]) for v in cards]
  Ahs=sum_poly([sc(w[0],ha),sc(w[1],hb)])
  Z0=add(Ahs,sc(L,-alpha))
  K,rem=qr(Z0,nodal([s,y]));assert not rem and len(K)==3
  V=Nested(monic_u(K));z=V.gen();gx=V(g);x=1-gx
  yield V,gx,x,V(s)*gx,V(y)*gx,z*gx

def nodal_u(pegs):
 out=[[1]]
 for root in pegs:
  arr=[[] for _ in range(len(out)+1)]
  for i,v in enumerate(out):
   arr[i]=add(arr[i],sc(mul(v,root),-1));arr[i+1]=add(arr[i+1],v)
  out=arr
 return out

def integrate(V,a,shift=0):
 return sum_poly([sc(v,V(1)/(i+shift+1)) for i,v in enumerate(a)])

def tests(front,back,p,t):
 for V,g,x,s,y,z in third(front,p,t):
  b0,b1,b2=[V(x) for x in (0,1,2)]
  u=[b0,b1];C=[x,-g]
  D=[x-2*g,g] if back else [x,-2*g]
  P6=nodal_u([[r] for r in (s,y,z,x)]+[C,D])
  m0,m1=integrate(V,P6),integrate(V,P6,1)
  base=[[r] for r in (s,y,z)]
  Wc=add(mul(m0,integrate(V,nodal_u(base+[[x],D]),1)),
         sc(mul(m1,integrate(V,nodal_u(base+[[x],D]))),-1))
  Wd=add(mul(m0,integrate(V,nodal_u(base+[[x],C]),1)),
         sc(mul(m1,integrate(V,nodal_u(base+[[x],C]))),-1))
  Wx=add(mul(m0,integrate(V,nodal_u(base+[C,D]),1)),
         sc(mul(m1,integrate(V,nodal_u(base+[C,D]))),-1))
  k=[b1,b2,-b1]
  F9=add(mul(k,Wc),sc(Wx,-1))
  if back:F8=add(mul(k,Wd),sc(Wx,-1))
  else:
   H=[V(-2),V(1),V(4),V(-1)]
   M=add(mul([V(1),V(4),V(-4)],H),[V(0),V(0),V(-8),V(12)])
   F8=add(mul(M,Wd),sc(mul(H,Wx),-1))
  assert F9 and F9[0]==0
  F9=F9[1:]
  assert len(F9)==4
  F=monic_u(F9)
  multicol(F,F8).inv()
 return True
