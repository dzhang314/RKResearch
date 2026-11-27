"""Both literal fronts silent, reverse factor nonzero, independent Gauss double."""
from one_front_zero import *

def phase(F,front,hit):
 cv=lambda x:F(Epoly(JJ(x))) if x else F(0)
 A,B,m=map(cv,ends(front,1))
 return A,B,m,A if hit==0 else B
def pguards(F,r,g,x,z,c,d,hit):
 K=Pcoeff(F,r)
 sels=[g,x-z,z-r,ev(K,z),c-z,d-z,x-c,x-d,c-d]
 for i,w in ((10,x),(9,c),(8,d)):
  if i!=hit:sels.extend([w-r,ev(K,w)])
 return sels
def val_pnum(U,N,D):
 return sum_poly([sc(mul(power(N,j),power(D,3-j)),p) for j,p in enumerate(PX)])
def tail_univ(U,X,Z,C,D,pX,pC,pD,k,H,Q):
 F9=add(mul(add(X,sc(Z,-1)),pC),sc(mul(mul(k,add(C,sc(Z,-1))),pX),-1))
 F8=add(mul(mul(H,add(X,sc(Z,-1))),pD),sc(mul(mul(Q,add(D,sc(Z,-1))),pX),-1))
 FX=add(mul(mul(mul(k,add(C,sc(Z,-1))),H),pD),sc(mul(mul(Q,add(D,sc(Z,-1))),pC),-1))
 return {9:F8,8:F9,10:FX}

@lru_cache(None)
def hit_tail(front,zslot,rear,hit):
 U=B0
 A,B,m,Z0=phase(U,front,zslot)
 u=[U(0),U(1)];k=[U(1),U(2),U(-1)]
 D9=[U(1),U(1)];D8=[U(3),U(-1)] if rear else [U(1),U(2)]
 D0={10:[U(1)],9:D9,8:D8}[hit]
 G0=1-R0
 X=add(D0,[-G0]);Z=[G0*Z0]
 C=add(D0,sc(D9,-G0));D=add(D0,sc(D8,-G0))
 H=[U(1)] if rear else [U(-2),U(1),U(4),U(-1)]
 Q=k if rear else sc(mul(k,[U(2),U(3),U(-12),U(4)]),-1)
 pX,pC,pD=(val_pnum(U,n,D0) for n in (X,C,D))
 F=tail_univ(U,X,Z,C,D,pX,pC,pD,k,H,Q)[hit]
 vv=mul(mul(D0,k),H)
 for v in (add(X,sc(Z,-1)),add(C,sc(Z,-1)),add(D,sc(Z,-1)),
           add(Z,sc(D0,R0*-1)),val_pnum(U,Z,D0),
           add(X,sc(C,-1)),add(X,sc(D,-1)),add(C,sc(D,-1))):
  vv=mul(vv,v)
 for i,nn,pp in ((10,X,pX),(9,C,pC),(8,D,pD)):
  if i!=hit:vv=mul(vv,mul(add(nn,sc(D0,-R0)),pp))
 assert vv and F
 FF=strip(F,vv)
 print('known tail double exact gap degree',front,zslot,rear,hit,len(FF)-1,flush=True)
 return FF

@lru_cache(None)
def star_front(front,zslot):
 U=B0
 A,B,m,Z0=phase(U,front,zslot)
 g=[U(0),U(1)];X=[U(1),U(-1)];Z=sc(g,Z0);Y=[U(1),U(-2)]
 XZ=add(X,sc(Z,-1));YZ=add(Y,sc(Z,-1))
 Xp,Yp=subst(PX,X),subst(PX,Y)
 Yd=subst(deriv(PX),Y)
 g2=mul(g,g);p3=PX[3]
 aa=mul(g2,add([PX[2]],sc(add(sc(Y,2),Z),p3)))
 bb=add(Yp,sc(mul(YZ,Yd),-1))
 assert len(gcdp(aa,bb))==1
 FF=sum_poly([mul(mul(aa,XZ),Yd),sc(mul(mul(XZ,g2),bb),-p3),
              sc(mul(add(sc(aa,2),bb),Xp),-1)])
 vv=mul(mul(mul(g,XZ),aa),mul(add(X,[-R0]),Xp))
 for v in (add(Z,[-R0]),subst(PX,Z),bb,add(aa,bb),add(sc(aa,2),bb),
           add(mul(aa,mul(YZ,YZ)),mul(g2,bb)),
           add(mul(aa,power(add(Y,[-R0]),2)),mul(g2,bb))):
  vv=mul(vv,v)
 assert FF and vv
 M=strip(FF,vv)
 print('exact star diagonal degree',front,zslot,len(M)-1,flush=True)
 return M,aa,bb

def mod_base(p,t):
 U=Bfield(nmod_poly(list(Lco),p),p,t)
 R0=U(nmod_poly([0,1],p))
 return U,R0

def basehit(front,zslot,rear,hit,p,t):
 M0=hit_tail(front,zslot,rear,hit)
 if len(M0)<=1:return
 F,rr=mod_base(p,t)
 U=Tower(list(map(F,M0)));u=U.gen();r=U(rr)
 den={10:U(1),9:1+u,8:3-u if rear else 1+2*u}[hit]
 g=(1-r)/den
 yield U,r,g,u

def basestar(front,zslot,p,t):
 M0,a,b=star_front(front,zslot)
 if len(M0)<=1:return
 F,rr=mod_base(p,t)
 U=Tower(list(map(F,M0)));g=U.gen();r=U(rr)
 a,b=ev(list(map(U,a)),g),ev(list(map(U,b)),g)
 S=Nested([b/a,U(0),U(1)]);v=S.gen()
 yield S,S(r),S(g),1+v

def data(front,zslot,rear,hit,F,r,g,u):
 k=1+2*u-u*u
 k.inv()
 if not rear:(-2+u+4*u*u-u**3).inv()
 A,B,m,Z=phase(F,front,zslot)
 x,c,d=1-g,1-g*(1+u),1-g*(3-u if rear else 1+2*u)
 z=g*Z
 X,C,D,R=x/g,c/g,d/g,r/g
 if hit:assert {10:X,9:C,8:D}[hit]==R
 for v in pguards(F,r,g,x,z,c,d,hit):v.inv()
 ha,hb=(A-1)/2,(B-1-m)/2
 H4=[F(Epoly(JJ(v))) for v in pol(h4(front),lambda v:v)]
 S=[w*g**j for j,w in enumerate(Pcoeff(F,r))]
 S=sc(S,(ha if zslot==0 else hb)/ev(S,Z))
 return X,C,D,R,A,B,m,Z,ha,hb,S,H4

def front_core(F,r,g,u,front,zslot,rear,hit):
 X,C,D,R,A,B,m,Z,ha,hb,S,H4=data(front,zslot,rear,hit,F,r,g,u)
 pegs=[X,C,D]+([] if hit else [R])
 if not hit:
  Y=two_pivots(F,g,pegs)
  hz=ev(H4,R)
  do5(F,g,X,R,A,B,m,Z,ha,hb,S,H4,pegs,R,hz,Y,1,False)
  W=Nested(Y);s=W.gen()
  cc=[W(v) for v in (g,X,R,A,B,m,Z,ha,hb)]
  Sw,Hw=[list(map(W,f)) for f in (S,H4)]
  hv=ev(Hw,s)
  if conditional_zero(W,hv-ev(Sw,s)):return
  Yn,re=qr(list(map(W,Y)),[-s,W(1)]);assert not re
  do5(W,*cc,Sw,Hw,list(map(W,pegs)),s,hv,Yn,2,False)
  return
 # If the fourth stage is the other active r, row five must be singleton.
 h=ev(H4,R)
 tr=A**3+A-1-A**4/4 if zslot==0 else B**3+B-1-m+m*A**3-B**4/4
 ar=ha if zslot==0 else hb+m*ha
 QT,QA=slopes(A,B,m,ha,hb,R,h,ar,tr,Z)
 T,U=row5(F,A,B,R,ha,hb,h,QT,QA,S)
 # The one always-padded root is the on-profile literal front (separate from active rows).
 T,er=qr(T,[-Z,F(1)]);assert not er and len(T)==4
 U,er=qr(U,[-Z,F(1)]);assert not er and len(U)==4
 multicol(mon(T),U).inv()
 # Otherwise row four itself is a fourth quadrature peg.
 Y=add(H4,sc(S,-1))
 Y,er=qr(Y,[-Z,F(1)]);assert not er and len(Y)==3
 W=Nested(mon(Y));s=W.gen()
 cc=[W(v) for v in (g,X,R,A,B,m,Z,ha,hb)]
 Sw,Hw=[list(map(W,f)) for f in (S,H4)]
 pp=list(map(W,pegs))+[s]
 Yn=two_pivots(W,W(g),pp)
 do5(W,*cc,Sw,Hw,pp,s,ev(Hw,s),Yn,2,False)

def verify(front,zslot,rear,hit,p,t):
 assert hit or rear # The three-singleton arithmetic case has its own exact projection.
 data0=basehit(front,zslot,rear,hit,p,t) if hit else basestar(front,zslot,p,t)
 for F,r,g,u in data0:front_core(F,r,g,u,front,zslot,rear,hit)
 return True
