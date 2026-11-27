"""Independent exact projections, then physical/virtual row-five terminal gates."""
from extra_active import *

def base_finite(Y,p,t):
 B=Bfield(nmod_poly([0,1],p),p,t)
 M=nmod_poly([int(B(v).x[0]) for v in Y],p)
 assert M.degree()==len(Y)-1 and M.leading_coefficient()==1
 for M0,_ in M.factor()[1]:
  F=Bfield(M0,p,t);gamma=F(nmod_poly([0,1],p))
  yield F,gamma

def star_fields(front,p,t):
 G,A,B,X,MM=star_projection(front)
 # The exact guarded all-zero tail coefficient branch is empty.
 assert len(X)==1
 for F,gamma in base_finite(G,p,t):
  V=-ev(list(map(F,A)),gamma)/ev(list(map(F,B)),gamma)
  U=Tower([-V,F(0),F(1)]);u0=1+U.gen()
  # In the normal case the two exact candidate equations hold by algebra.
  T,N,_=polys(front,True)
  coeff=lambda F0:coefficients(U,F0,U(gamma),1)
  assert not ev(coeff(T),u0) and not ev(coeff(N),u0)
  yield U,U(gamma),u0,[]

@lru_cache(None)
def arithmetic_projection(front):
 T,H,_=polys(front,False)
 R=can(T.resultant(H,1))
 G=gcoeff(R);assert G
 guard=physical_guard(front)
 M=mon(guarded(G,guard))
 TL=exact_uc(T)[-1]
 singular=gcdp(M,TL);reg=mon(guarded(M,[TL]))
 print('arithmetic extra projection',front,len(G)-1,len(M)-1,len(singular)-1,len(reg)-1,flush=True)
 return T,H,singular,reg

def ara_fields(front,p,t):
 T,H,sing,reg=arithmetic_projection(front)
 assert len(sing)==1
 ac=exact_uc(T)[0]
 Z=gcdp(reg,ac);N=mon(guarded(reg,[ac]))
 print('exact separate zero-gap subfactor',front,len(Z)-1,len(N)-1,flush=True)
 for G,j in ((Z,True),(N,False)):
  if len(G)<=1:continue
  for F,gamma in base_finite(G,p,t):
   T0=coefficients(F,T,gamma,1);H0=coefficients(F,H,gamma,1)
   assert len(T0)==6
   if j:
    assert not T0[0]
    T0=T0[1:] # Actual u!=0; split by the exact constant coefficient.
   U=Tower(mon(T0));u0=U.gen()
   e=ev(list(map(U,H0)),u0)
   yield U,U(gamma),u0,[e]

def row5_elim(U,g,front):
 A,B,m,ha,hb,H4,qA,qB,q0,q1,*_=phases(front)
 A,B,m,ha,hb=map(U,(A,B,m,ha,hb));H4=list(map(U,H4))
 a,b=(ev(list(map(U,Q)),g) for Q in (q0,q1))
 F0=first5(U,A,B,m,ha,hb,[],H4)
 F1=first5(U,A,B,m,ha,hb,[U(1)],H4)
 E=add(mul(F0,[a,b]),mul(add(F1,sc(F0,-1)),[U(v)*g**j for j,v in enumerate(Lco)]))
 Q,re=qr(E,list(map(U,nodal([A,B]))));assert not re
 return Q,(A,B,a,b)

def scaled_quadratic_resultant(F,E,Y):
 assert len(Y)==3
 if not Y[2]:return F(0)
 X=list(E)
 while len(X)>2:X=add(sc(X,Y[2]),[F(0)]*(len(X)-3)+sc(Y,-X[-1]))
 X=X+[F(0)]*(2-len(X))
 l,m=X
 return Y[2]*l*l-Y[1]*l*m+Y[0]*m*m

def homogenized(F,E,num,den):
 d=len(E)-1
 return sum(c*num**j*den**(d-j) for j,c in enumerate(E))

def finish(U,g,u,front,rear,ee):
 E,(A,B,a,b)=row5_elim(U,g,front)
 x=1-g;c=x-g*u;d=x-g*(2-u if rear else 2*u)
 k=1+2*u-u*u
 L=list(map(U,Lco));qx=g*a+b*x;qc=g*a+b*c
 Cw,Xw=ev(L,c)*qx,ev(L,x)*qc
 a9=Cw-k*Xw;b9=x*Cw-c*k*Xw
 # The possible first ordinary or virtual row five:
 # either y is one of the two remaining active nodes, or it is the separate root.
 pts=[g*A,g*B,x,c,d]
 M=moment(U,pts,[g*a,b],4)
 m0,m1,m2,m3=M
 Y=[m1*m3-m2*m2,(m1*m2-m0*m3)*g,(m0*m2-m1*m1)*g*g]
 M1=scaled_quadratic_resultant(U,E,Y)
 M2=homogenized(U,E,b9,g*a9)
 span_unit(U,*ee,M1)
 span_unit(U,*ee,M2)
 return True

def verify(front,rear,p,t):
 for U,g,u,e in (star_fields(front,p,t) if rear else ara_fields(front,p,t)):finish(U,g,u,front,rear,e)
 return True
