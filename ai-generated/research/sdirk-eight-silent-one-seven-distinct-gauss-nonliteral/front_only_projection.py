"""Reusable literal fourth/fifth projection for the p0 cubic profile."""
from gauss_small_nonliteral import *
from gauss_tail_nonliteral import B0,R0,Pvar
from arithmetic_nonzero import pseudo
from flint import fmpq_mpoly_ctx

CX=fmpq_mpoly_ctx.get(['y','s','g','r','t'])
y,s,g,r,t=CX.gens()
L4=lambda X:sum(v*X**i for i,v in enumerate(Lco))
LP=L4(r)/70;LT=t*t-CX.constant(Q(1)/2)
p0=lambda X:70*X**3+(-140+70*r)*X**2+(90-140*r+70*r**2)*X-20+90*r-140*r**2+70*r**3
def C(M):
 if isinstance(M,int):M=CX.constant(M)
 return (M%LP)%LT
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
def termr(ps,w):
 return sum((v.v.a[j]+t*v.v.b[j])*r**j*w**i for i,v in enumerate(ps) for j in range(v.v.degree()+1))
def ats(F):
 return C(sum(a*s**(i+j)*g**k*r**l*t**m for (i,j,k,l,m),a in F.to_dict().items()))
def atR(F):
 n=F.degrees()[0]
 return C(sum(a*s**j*g**(k+n-i)*r**(l+i)*t**m for (i,j,k,l,m),a in F.to_dict().items()))
def bsg(F):
 T={}
 for (i,j,k,h,l),v in C(F).to_dict().items():
  assert not i and h<=3 and l<=1
  e=E(Pvar([0]*h+[v]))
  if l:e=E(0,e.a)
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
 H=term0(H4,s);Q0=C(p0(g*a));P=C(E0(hh)*p0(g*y))
 U=C(H*Q0-ats(P))
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
 guards=list(map(bg,[g,Q0]))
 E=C(FT.resultant(FA,0))
 assert E and not E.degrees()[0]
 print('front Gauss residual degrees',f,i,E.degrees(),flush=True)
 q,Qphi=prim_s(Phi);p,QE=prim_s(E)
 X,Y=bsg(Qphi),bsg(QE)
 assert len(X)==3
 Z=pseudo(Y,X)
 Wr=C(sum(termr(a,g)*s**i for i,a in enumerate(Z)))
 Rg=bg(C(Qphi.resultant(Wr,1)))
 assert Rg
 N=mon(guarded(mul(mul(mul(q,p),X[-1]),Rg),guards))
 Th,Ah=atR(T0),atR(A0)
 Hr=bg(C(Th.resultant(Ah,1)))
 assert Hr
 Hole=mon(guarded(Hr,guards))
 G=gcdp(N,Hole)
 assert (len(N)-1,len(Hole)-1,len(G)-1)==(114,7,0)
 print('literal fifth projection exact degrees',f,i,len(N)-1,len(Hole)-1,'intersection',len(G)-1,flush=True)
 return N,Hole,Phi,FT,FA,T0,A0
