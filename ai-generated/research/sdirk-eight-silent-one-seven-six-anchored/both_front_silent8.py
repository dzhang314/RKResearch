"""Both literal front rows active, separate reverse-zero physical eight."""
from both_front_active8 import *

def context(U,A,B,m,ha,hb,C,H4):
 d=(hb-ha)/(B-A)
 S=[ha-A*d,d]
 AA=nodal([A,B])
 e,er=qr(add(H4,sc(S,-1)),AA);assert not er and len(e)==2
 tA=A**3+A-1-A**4/4
 tB=B**3+B-1-m+m*A**3-B**4/4
 def line(a,b):
  k=(b/hb-a/ha)/(B-A);return [a/ha-A*k,k]
 TA=line(tA,tB);QA=line(ha,hb+m*ha)
 return S,AA,e,TA,QA

def front5(U,A,B,S,e,TA,QA,y,h):
 m0=y-1-2*h
 m1=y*y/2-y-2*h
 m2=y**3/3-y*y-4*h/3
 A0=m2-(A+B)*m1+A*B*m0
 T0=y**3-y**4/4+2*h+(A+B)*m2-A*B*m1-ev(TA,y)*h
 B0=h+S[0]*m0+S[1]*m1+e[0]*A0-ev(QA,y)*h-e[1]*T0
 return A0,T0,B0

def nextgate(U,A,B,S,e,TA,QA,C,Z,y,h):
 H2=add(S,sc(nodal([A,B]),ev(e,Z)))
 F3=nodal([A,B,Z])
 M0=add([U(-1),U(1)],sc(C,-2))
 M1=add([U(0),U(-1),U(1)/2],sc(C,-2))
 M2=add([U(0),U(0),U(-1),U(1)/3],sc(C,-U(4)/3))
 M3=sum_poly([[U(0),U(0),U(0),U(-1),U(1)/4],mul(TA,C),sc(C,-2)])
 M=[M0,M1,M2,M3]
 v0=sum_poly([mul(QA,C),sc(C,-1),sc(sum_poly([sc(q,w) for q,w in zip(M,H2)]),-1)])
 v1=sum_poly([sc(q,w) for q,w in zip(M,F3)])
 return add(sc(v0,ev(F3,y)),sc(v1,ev(H2,y)-h))

@lru_cache(None)
def tail_projection(front,M,rn):
 F,g,X,R,A,B,r,ha,hb,p,q,C,H4=model(front,M)
 u,k,c,d,H,q3,A9,B9,A8,B8=tail_poly(F,X,R,C,True)
 Z=add([X],sc(mul(k,[F(-2),F(1)]),F(1)/2))
 if rn:return [-X+R,F(1)]
 z0=add(B9,sc(mul(A9,Z),-1))
 assert z0
 guards=mul(mul(u,k),mul(add(c,[-R]),subst(C,c)))
 guards=mul(guards,mul(add(Z,[-X]),add(Z,sc(c,-1))))
 z0=strip(z0,guards)
 assert len(z0)==4
 print('silent eighth reverse tail projection',front,M.degree(),len(z0)-1,flush=True)
 return z0

@lru_cache(None)
def early_projection(front,M):
 F,g,X,R,A,B,r,ha,hb,p,q,C,H4=model(front,M)
 U=F;H4=list(H4)
 E=first5(U,A,B,r,ha,hb,C,H4)
 assert E
 E=strip(E,list(map(F,nodal([A,B,X]))))
 assert len(E)==4
 print('silent8 both known r copies early fifth projection',front,M.degree(),len(E)-1,flush=True)
 return E

def reconstruct(U,g,pegs):
 D=nodal([g*z for z in pegs]);J=lambda j:intp(U,D,j)
 A,B,C,D0=[J(j) for j in range(4)]
 hh=A*C-B*B
 return [(B*D0-C*C)/(hh*g*g),(B*C-A*D0)/(hh*g),U(1)]

def verify(front,M,rn,p,t,gap=None):
 F0,g,X,R,A,B,r,ha,hb,P,Q,C,H4=model(front,M)
 copies=int(R==A)+int(R==B)+int(rn)
 if A==R or B==R:
  S0,AA0,e0,TA0,QA0=context(F0,A,B,r,ha,hb,C,H4)
  hh=ha if A==R else hb
  assert not front5(F0,A,B,S0,e0,TA0,QA0,R,hh)[2]
 d0=(g,X,R,A,B,r,ha,hb,P,Q,C,H4)
 m0=tail_projection(front,M,rn) if gap is None else [-gap,F0(1)]
 if len(m0)==1:return True
 for U,u in reduced(M,p,t,m0):
  g,X,R,A,B,r,ha,hb=map(U,d0[:8]);P,Q,C,H4=[list(map(U,X)) for X in d0[8:12]]
  c=X-u
  pegs=[A,B,X,c]
  if copies==0:pegs.append(R)
  if copies==2:pegs.pop(0 if d0[3]==d0[2] else 1)
  D=nodal([g*z for z in pegs]);J=lambda j:intp(U,D,j)
  if copies==0:
   (J(0)*J(2)-J(1)*J(1)).inv()
   continue
  if copies==1:
   Y=reconstruct(U,g,pegs)
   E=first5(U,A,B,r,ha,hb,C,H4)
   multicol(Y,E).inv()
   S,AA,e,TA,QA=context(U,A,B,r,ha,hb,C,H4)
   a0,t0,F0=front5(U,A,B,S,e,TA,QA,R,U(0))
   a1,t1,F1=front5(U,A,B,S,e,TA,QA,R,U(1))
   H=-F0/(F1-F0)
   if d0[3]==d0[2] or d0[4]==d0[2]:
    assert H==(ha if d0[3]==d0[2] else hb)
    continue
   a0,t0,F0=front5(U,A,B,S,e,TA,QA,R,H)
   assert not F0
   Z=-t0/a0
   G0=nextgate(U,A,B,S,e,TA,QA,C,Z,R,H)
   multicol(Y,G0).inv()
   continue
  W=early_projection(front,M)
  if len(W)<=1:continue
  from equal_undetected_front import Nested
  T=Nested(list(map(U,W)));y=T.gen()
  g,X,R,A,B,r,ha,hb=map(T,(g,X,R,A,B,r,ha,hb));C,H4=[list(map(T,X)) for X in (C,H4)]
  S,AA,e,TA,QA=context(T,A,B,r,ha,hb,C,H4)
  h=ev(C,y);a0,t0,F0=front5(T,A,B,S,e,TA,QA,y,h)
  assert not F0
  Z=-t0/a0
  Y=reconstruct(T,g,[A,B,X,y])
  G0=nextgate(T,A,B,S,e,TA,QA,C,Z,y,h)
  multicol(Y,G0).inv()
 return True
