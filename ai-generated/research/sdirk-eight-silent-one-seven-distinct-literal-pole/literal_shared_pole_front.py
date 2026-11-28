"""Literal-front pole: reverse scalar intersections and two physical silent slopes."""
from no_extra import *
from extra_active import exact_uc
from both_front_silent8 import context

@lru_cache(None)
def frontdata(f,i):
 F=F2
 A,B,m=map(lambda v:cv(F,v),ends(f,1));ha,hb=(A-1)/2,(B-1-m)/2
 a,b,h=(A,B,ha) if i==0 else (B,A,hb)
 H4=[cv(F,v) for v in pol(h4(f),lambda v:v)]
 L0,AA,e,QT,QA=context(F,A,B,m,ha,hb,None,H4)
 tau,ah=ev(QT,a),ev(QA,a)
 HS=term(H4,y);ap,bp,aa=map(expr,(A,B,a))
 M0=y-1-2*HS;M1=y*y/2-y-2*HS
 Ta=(bp*M0-M1)*expr((B-A).inv());Tb=M0-Ta
 T4=can(y**3-y**4/4+2*HS+Ta*ap**3+Tb*bp**3)
 A4=can(HS+Ta*expr(ha)+Tb*expr(hb))
 XT=exdiv(can(T4-expr(tau)*HS),y-aa)
 XA=exdiv(can(A4-expr(ah)*HS),y-aa)
 J=-F(4)/3+2*(A+B)-2*A*B
 dT=[2-F(4)/3*(A+B)+2*A*B,J]
 dA=add([1-2*L0[0]-2*L0[1]],sc(e,J))
 return A,B,m,ha,hb,a,b,h,H4,L0,e,tau,ah,HS,XT,XA,dT,dA,T4,A4

def silent5(f,i):
 A,B,m,ha,hb,a,b,h,H4,L0,e,tau,ah,HS,XT,XA,dT,dA,T4,A4=frontdata(f,i)
 D=can(HS*(term(dT,y)-expr(tau))-XT*expr(b-a))
 E=can(HS*(term(dA,y)-expr(ah))-XA*expr(b-a))
 x,y0=exact_uc_y(D),exact_uc_y(E)
 G=gcdp(x,y0)
 # This receipt includes all H4=0 degeneracies as well.
 assert len(G)==1,(f,i,G)
 return len(G)-1

def exact_uc_y(M):
 X={}
 for (i,j,k),v in parts(M).items():
  if v:
   assert not j and not k
   X[i]=v
 return [X.get(i,F2(0)) for i in range(max(X,default=-1)+1)]

@lru_cache(None)
def tails(f,i,kind):
 A,B,m,ha,hb,a,b,h,*_=frontdata(f,i)
 L4=lambda z:sum(v*z**j for j,v in enumerate(Lco))
 a,b=map(expr,(a,b))
 x=1-g;c=x-g*u
 k=1+2*u-u*u
 z=g*b
 px,pc=L4(x),L4(c)
 qx,qc=x-z,c-z
 F9=exdiv(can(pc*qx*qx-k*px*qc*qc),u)
 if kind is None:
  F8=can(2*qx+g*k*(u-2))
 else:
  d=x-g*(2-u if kind else 2*u)
  pd,qd=L4(d),d-z
  if kind:
   F8=exdiv(can(pd*qx*qx-k*px*qd*qd),u-2)
   # At u=1 these two ordinary stage clocks coincide. Replace F8 by its
   # independent divided relation, valid after excluding u=1.
   F8=exdiv(can(F8+F9),u-1)
  else:
   H=-2+u+4*u*u-u**3;T=4*u**3-12*u*u+3*u+2
   F8=exdiv(can(H*pd*qx*qx+k*T*px*qd*qd),u)
   # Both ratios have the unique exact forbidden zero-gap padding, but
   # F8 may retain a further exact factor; examine it without assumptions.
   while True:
    J,R=divmod(F8,u)
    if can(R):break
    F8=can(J)
 gl=[g,qx,L4(z),px,L4(g*a),x-g*a]
 guards=[gcoeff(can(v)) for v in gl]
 J=gcoeff(can(F9.resultant(F8,1)))
 G=mon(guarded(J,guards))
 U=exact_uc(F9)
 V=exact_uc(F8)
 assert len(G)-1==({True:22,False:44,None:17}[kind])
 return G,U,V
