"""Reusable finite tail projections at the literal reverse-root clock."""
from arithmetic_nonzero import generic,raw_arm,pguards,phase,mod_base,basehit,basestar
from one_front_zero import *

def arithmetic_pts(front,zslot,p,t0):
 M,l,m,hh,lead,F,J=generic(front,zslot)
 assert len(hh)==1
 V,Rm=mod_base(p,t0)
 a,b,c=F
 if len(lead)>1:
  W=Tower(list(map(V,lead)));gg=W.gen()
  at=lambda q:ev(list(map(W,q)),gg)
  assert not at(c)
  at(b).inv()
  uu=-at(a)/at(b)
  ev([at(q) for q in J],uu).inv()
 if len(M)>1:
  W=Tower(list(map(V,M)));gg=W.gen()
  at=lambda q:ev(list(map(W,q)),gg)
  at(c).inv();at(m).inv()
  uu=-at(l)/at(m)
  assert not ev([at(q) for q in F],uu)
  assert not ev([at(q) for q in J],uu)
  yield W,W(Rm),gg,uu

def star_constant(front,zslot,rear,hit,p,t):
 if hit:yield from basehit(front,zslot,rear,hit,p,t)
 elif rear:yield from basestar(front,zslot,p,t)
 else:yield from arithmetic_pts(front,zslot,p,t)

def zgauss(front,zslot,rear,p,t):
 V,Rm=mod_base(p,t)
 Z=phase(V,front,zslot)[-1]
 K=Pcoeff(V,Rm)
 C=mon(subst(K,[V(0),Z]));assert len(C)==4
 W=Tower(C);g=W.gen();r=W(Rm);Z=W(Z)
 g.inv()
 x,z=1-g,g*Z
 (x-r).inv();(x-z).inv()
 T,rem=qr(list(map(W,K)),[-z,W(1)]);assert not rem and len(T)==3
 Tx=ev(T,x);Tx.inv()
 Tpx=T[1]+2*T[2]*x
 u=(g*Tpx+2*Tx)/(g*g*T[2]+Tx)
 d=lambda u:x-g*(2-u if rear else 2*u)
 c=lambda u:x-g*u
 kf=lambda u:1+2*u-u*u
 Hf=lambda u:W(1) if rear else -2+u+4*u*u-u**3
 qf=lambda u:kf(u) if rear else -kf(u)*(4*u**3-12*u*u+3*u+2)
 (Hf(u)*ev(T,d(u))-qf(u)*Tx).inv() # Both nonterminal tails singleton.
 (d(u)-r).inv() # Eighth is the sole tail r copy.
 u9=(x-r)/g
 (Hf(u9)*ev(T,d(u9))-qf(u9)*Tx).inv() # Ninth is the sole tail r copy.
 return True

@lru_cache(None)
def silent_z_projection(front,zslot,hit):
 U=B0
 Z=phase(U,front,zslot)[-1]
 u=[U(0),U(1)];k=[U(1),U(2),U(-1)]
 D=add([U(1)+Z],sc(mul(k,[U(-2),U(1)]),-U(1)/2))
 X=add(D,[-U(1)]);C=add(X,sc(u,-1))
 def pnum(M):return sum_poly([sc(mul(power(M,j),power(D,3-j)),p) for j,p in enumerate(PX)])
 r10=add(X,sc(D,-R0));r9=add(C,sc(D,-R0))
 if hit in (9,10):G=r9 if hit==9 else r10
 else:
  m=add(sc(u,2),mul(k,[U(-2),U(1)]))
  G=add(mul([U(-2),U(1)],pnum(C)),sc(mul(m,pnum(X)),-1))
  assert G and not G[0]
  G=G[1:]
 A=phase(U,front,1-zslot)[-1]
 guards=[D,u,k,[U(-2),U(1)],add(sc(u,2),mul(k,[U(-2),U(1)])),
         add([Z],sc(D,-R0)),add(X,[-A]),add(C,[-A]),[-R0*D[0]+A]+sc(D[1:],-R0),
         pnum([A])]
 if hit!=10:guards.extend([r10,pnum(X)])
 if hit!=9:guards.extend([r9,pnum(C)])
 for q in guards:
  if not q:return [U(1)]
 G=strip(G,polyprod(guards))
 print('literal shared-root silent eighth fixed gap',front,zslot,hit,len(G)-1,flush=True)
 return G

def polyprod(L):
 q=[B0(1)]
 for v in L:q=mul(q,v)
 return q

def silent_z_pts(front,zslot,hit,p,t):
 G=silent_z_projection(front,zslot,hit)
 if len(G)<=1:return
 F,rr=mod_base(p,t)
 U=Tower(list(map(F,G)));u=U.gen();r=U(rr)
 Z=phase(U,front,zslot)[-1]
 g=1/(1+Z-(1+2*u-u*u)*(u-2)/2)
 yield U,r,g,u
