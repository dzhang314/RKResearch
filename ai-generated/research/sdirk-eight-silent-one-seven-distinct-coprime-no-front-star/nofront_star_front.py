"""Front-only projection in the no-active-literal coprime star case."""
from literal_shared_pole_late import *
from nofront_star_tail import gauge
from shared_silent8_projection import ef,unef,eguard,eexact,epow,pseudo_e,sylvester_e
from arithmetic_nonzero import pseudo
from flint import fmpq_mpoly_ctx

CX=fmpq_mpoly_ctx.get(['y','s','g','t'])
y,s,g,t=CX.gens()
L4=lambda X:sum(v*X**i for i,v in enumerate(Lco))
LT=t*t-CX.constant(Q(1)/2)
p0=L4
B0=F2
def C(M):
 if isinstance(M,int):M=CX.constant(M)
 return M%LT
def div(F,D):
 A,B=divmod(F,D)
 return C(A),C(B)
def exdiv(F,D):
 A,B=div(F,D);assert not B
 return A
def E0(v):
 a=F2(v).v
 return a.a[0]+t*a.b[0]
def term0(ps,w):return sum(E0(v)*w**i for i,v in enumerate(ps))
def termr(ps,w):return term0(ps,w)
def ats(F):
 return C(sum(a*s**(i+j)*g**k*t**m for (i,j,k,m),a in F.to_dict().items()))
def bsg(F):
 T={}
 for (i,j,k,l),v in C(F).to_dict().items():
  assert not i and l<=1
  e=E(v,0) if not l else E(0,v)
  d=T.setdefault(j,{});d[k]=d.get(k,B0(0))+B0(e)
 return [trim([T.get(j,{}).get(k,B0(0)) for k in range(max(T.get(j,{}),default=-1)+1)])
         for j in range(max(T,default=-1)+1)]
def bg(F):
 Q=bsg(F);assert len(Q)<=1
 return Q[0] if Q else []
def prim_s(F):
 Z=bsg(F);G=[]
 for a in Z:
  if a:G=gcdp(G,a)
 if len(G)<=1:return [B0(1)],F
 v=[divp(a,G)[0] if a else [] for a in Z]
 return G,C(sum(termr(a,g)*s**i for i,a in enumerate(v)))

@lru_cache(None)
def front_polys(f,i):
 A,B,m,ha,hb,a,b,hh,H4,L0,e,tau,ah,HS,XT,XA,DT,DA,T4,A4=frontdata(f,i)
 A,B,a=map(E0,(A,B,a))
 A0,B0,_q0,_q1,_gs=gauge(f,i)
 q=lambda X:C(term0(_q0,g)+term0(_q1,g)*g*X)
 H=term0(H4,s);Q0=C(p0(g*a)*q(y));P=C(E0(hh)*q(a)*p0(g*y))
 U=C(H*ats(Q0)-ats(P))
 Phi=exdiv(U,s-a)
 m0=y-1;m1=y*y/2-y;m2=y**3/3-y*y
 J=m2-(A+B)*m1+A*B*m0
 T0=C(y**3-y**4/4+(A+B)*m2-A*B*m1+s*J)
 A0=C(E0(L0[0])*m0+E0(L0[1])*m1+term0(e,s)*J)
 T1=C(H*(term0(DT,s)-E0(tau))-term0(exact_uc_y(XT),s)*(y-a))
 A1=C(H*(term0(DA,s)-E0(ah))-term0(exact_uc_y(XA),s)*(y-a))
 FT=exdiv(C(H*T0*Q0+T1*P),y-a)
 FA=exdiv(C(H*A0*Q0+A1*P),y-a)
 FT,FTR=div(FT,y-s);FA,FAR=div(FA,y-s)
 assert not C(FTR-ats(T0)*Phi) and not C(FAR-ats(A0)*Phi)
 return Phi,FT,FA,T0,A0,Q0

@lru_cache(None)
def project(f,i):
 Phi,FT,FA,T0,A0,Q0=front_polys(f,i)
 guards=gauge(f,i)[-1]
 E=C(FT.resultant(FA,0))
 assert E and not E.degrees()[0]
 print('no-front star first resultant',f,i,E.degrees(),flush=True)
 X=list(map(ef,bsg(Phi)));Y=list(map(ef,bsg(E)))
 assert len(X)==4
 Z=pseudo_e(Y,X);assert Z
 n,m,j=len(X)-1,len(Y)-1,len(Z)-1
 R=sylvester_e(X,Z);assert R
 d=j+n*(m-n+1)-m
 if d:R=eexact(R,epow(X[-1],d))
 N=unef(eguard(R*X[-1],list(map(ef,guards))))
 assert len(N)-1==319
 print('no-front star guarded diagonal degree:',f,i,len(N)-1,flush=True)
 return N,Phi,FT,FA
