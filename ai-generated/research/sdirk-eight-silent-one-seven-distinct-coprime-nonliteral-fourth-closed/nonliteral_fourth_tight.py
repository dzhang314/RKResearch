"""Source-saturate true terminal guards and remove the arithmetic common top."""
from nonliteral_fourth_projection import *

def conj(F):
 d=F.to_dict()
 return CX.from_dict({a:v*(-1 if a[4] else 1) for a,v in d.items()})

def div_quadratic(F,D):
 A=conj(D)
 N=fold(D*A)
 Q,R=divmod(fold(F*A),N)
 assert N and not N.degrees()[4]
 if R:return None
 assert fold(Q*D)==F
 return Q

def strip_exact(F,D):
 assert F and D
 n=0
 while True:
  Q=div_quadratic(F,D)
  if Q is None:return F,n
  F=Q;n+=1

@lru_cache(None)
def tightened(f,i,star):
 J,T,V,D,Q0,P0,gg=profiles(f,i)
 X=1-g;Z=g*s;C=X-g*u;Xz=X-Z
 q0,q1=coeff_var(Q0,0)
 q=lambda x:fold(g*q0+x*q1)
 Qx=q(X);U=fold(Qx*Xz);Lx=L(X);k=1+2*u-u*u
 R=exdiv(fold(Qx*Xz*L(C)-k*q(C)*(C-Z)*Lx),u)
 if star:
  B0=Qx+q1*Xz-g*q1; B1=-g*q1
  P=exdiv(fold(L(C)-k*Lx),u)
  pp=coeff_var(subst_var(P,2,u+1),2);assert len(pp)==4
  RG=coeff_var(subst_var(R,2,u+1),2);assert len(RG)==4
  M=fold(U*(pp[0]*pp[3]-pp[1]*pp[2])+g*Lx*(B0*(2*pp[3]+pp[1])-B1*(pp[0]+2*pp[2])))
  assert fold(RG[0]*RG[3]-RG[1]*RG[2]-U*M)==CX.constant(0)
  W=fold(sum(F*u**j for j,F in enumerate(RG)))
  for a in gg[:4]:W,_=strip_exact(W,a)
  RG=coeff_var(W,2)
  R=[RG[0],RG[2]];S=[RG[1],RG[3]]
  St=M
 else:
  d=X-2*g*u
  H=-2+u+4*u*u-u**3;T0=4*u**3-12*u*u+3*u+2
  S=exdiv(fold(H*Qx*Xz*L(d)+k*T0*q(d)*(d-Z)*Lx),u)
  RC=coeff_var(R,2);SC=coeff_var(S,2)
  assert len(RC)==4 and len(SC)==7 and not fold(SC[-1]+16*RC[-1])
  S=fold(S+16*u**3*R)
  SC=coeff_var(S,2)
  assert len(SC)==6 and not fold(SC[-1]-8*RC[-2]-64*RC[-1])
  for a in gg[:4]:
   R,_=strip_exact(R,a);S,_=strip_exact(S,a)
  St=fold(R.resultant(S,2))
 for a in gg[:4]:Qx,_=strip_exact(Qx,a)
 n=[]
 for a in [*gg[:4],Qx,Xz]:
  St,k0=strip_exact(St,a)
  n.append(k0)
 assert St
 print('j4 tightened exact rear projection',f,i,star,St.degrees(),n,flush=True)
 return St,R,S

@lru_cache(None)
def tight_profiles(f,i):
 J,T,A,D,Q0,P0,gg=profiles(f,i)
 J,n=strip_exact(J,gg[3]);T,m=strip_exact(T,gg[3]);A,l=strip_exact(A,gg[3])
 assert (n,m,l)==((0,0,0) if f else (3,1,1))
 print('j4 tightened front:',f,i,J.degrees(),(n,m,l),flush=True)
 return J,T,A,D,Q0,P0,gg
