"""Exact early projection for a singleton literal active front and sole late root."""
from one_front_zero import *
from both_front_silent8 import context as literal_context
from arithmetic_nonzero import guarded
from flint import fmpq_mpoly_ctx
Dctx=fmpq_mpoly_ctx.get(['y','s','g','r','t'])
y,s,g,r,t=Dctx.gens()

def expr(q):
 q=B0(q).v
 return sum(c*r**i for i,c in enumerate(q.a))+t*sum(c*r**i for i,c in enumerate(q.b))
def term(a,v):return sum(expr(q)*v**j for j,q in enumerate(a))

def parts(F):
 X={}
 for (i,j,k,l,m),q in F.to_dict().items():
  D=X.setdefault((i,j,k),[[],[]])[m%2]
  D.extend([Q(0)]*(l+1-len(D)));D[l]+=q/(2**(m//2))
 return {mon:B0(E(*map(P,terms))) for mon,terms in X.items()}

def can(F):
 return sum((expr(q)*y**i*s**j*g**k for (i,j,k),q in parts(F).items() if q),Dctx.constant(0))

def rdiv(F,m):
 f,b=divmod(F,m)
 return can(f),can(b)

def sr(F,idx):
 # homogeneous substitution for s=r/g or y=r/g
 assert idx in (0,1)
 degree=F.degrees()[idx]
 X=0
 for e,v in F.to_dict().items():
  i,j,k,l,m=e
  if idx==0:X+=v*s**j*g**(k+degree-i)*r**(l+i)*t**m
  else:X+=v*y**i*g**(k+degree-j)*r**(l+j)*t**m
 return can(X)

def coeff1(F,axis):
 W=parts(F)
 out={}
 for e,q in W.items():
  if q:
   assert all(v==0 for i,v in enumerate(e) if i!=axis)
   out[e[axis]]=q
 return [out.get(i,B0(0)) for i in range(max(out,default=-1)+1)]

@lru_cache(None)
def core(front,slot):
 F=B0;cv=lambda a:F(Epoly(JJ(a))) if a else F(0)
 A,B,m=map(cv,ends(front,1));L=A if slot==0 else B
 ha,hb=(A-1)/2,(B-1-m)/2
 HH=ha if slot==0 else hb
 H4=[cv(v) for v in pol(h4(front),lambda q:q)]
 S,AA,e,TA,QA=literal_context(F,A,B,m,ha,hb,None,H4)
 ta,qa=ev(TA,L),ev(QA,L)
 m0=add([F(-1),F(1)],sc(H4,-2));m1=add([F(0),F(-1),F(1)/2],sc(H4,-2))
 wa=sc(add(sc(m0,B),sc(m1,-1)),1/(B-A));wb=add(m0,sc(wa,-1))
 TT=sum_poly([[F(0),F(0),F(0),F(1),-F(1)/4],sc(H4,2),sc(wa,A**3),sc(wb,B**3)])
 AA=sum_poly([H4,sc(wa,ha),sc(wb,hb)])
 XT,rt=qr(add(TT,sc(H4,-ta)),[-L,F(1)])
 XA,ra=qr(add(AA,sc(H4,-qa)),[-L,F(1)])
 assert not rt and not ra
 aa,bb,ll=map(expr,(A,B,L));H4s=term(H4,s)
 dH=-F(4)/3+2*(A+B)-2*A*B
 DT=[2-F(4)/3*(A+B)+2*A*B,dH]
 DA=add([1-2*S[0]-2*S[1]],sc(e,dH))
 Dup=gcdp(add(mul(DT,H4),sc(TT,-1)),add(mul(DA,H4),sc(AA,-1)))
 assert len(guarded(Dup,[[-A,F(1)],[-B,F(1)]]))==1
 assert len(gcdp(H4,AA))==1
 M0=y-1;M1=y*y/2-y;M2=y**3/3-y*y
 J0=M2-(aa+bb)*M1+aa*bb*M0
 T0=y**3-y**4/4+(aa+bb)*M2-aa*bb*M1+s*J0
 A0=expr(S[0])*M0+expr(S[1])*M1+term(e,s)*J0
 T1=H4s*(term(DT,s)-expr(ta))-term(XT,s)*(y-ll)
 A1=H4s*(term(DA,s)-expr(qa))-term(XA,s)*(y-ll)
 D=term(PX,g*ll)
 hY=expr(HH)*term(PX,g*y)
 f0=can(D*H4s*T0+hY*T1)
 f1=can(D*H4s*A0+hY*A1)
 E0,re=rdiv(f0,y-ll);assert not re
 E1,re=rdiv(f1,y-ll);assert not re
 F0=can(D*H4s-expr(HH)*term(PX,g*s))
 Phi,re=rdiv(F0,s-ll);assert not re
 S0,r0=rdiv(E0,y-s)
 S1,r1=rdiv(E1,y-s)
 # Check the exact omitted remainder, not just an arithmetic coincidence at sampled clocks.
 def at_s(T):
  return sum((v*s**(a+b)*g**c*r**d*t**e for (a,b,c,d,e),v in T.to_dict().items()),Dctx.constant(0))
 assert not can(r0-Phi*at_s(T0)) and not can(r1-Phi*at_s(A0))
 Rdet=can(T0*A1-A0*T1)
 return Phi,E0,E1,S0,S1,Rdet,D,F0,H4,TT,AA,DT,DA,T0,A0,T1,A1

@lru_cache(None)
def candidates(front,slot,branch):
 Phi,E0,E1,S0,S1,Rdet,D,Fp,H4,*_=core(front,slot)
 cv=lambda a:B0(Epoly(JJ(a))) if a else B0(0)
 A,B,_=map(cv,ends(front,1));L=A if slot==0 else B
 if branch==4: # fourth r; fifth on singleton profile
  T=sr(E0,1);U=sr(E1,1)
  print('s=r exact y degrees',T.degrees(),U.degrees(),flush=True)
  G=can(T.resultant(U,0))
 elif branch==5: # fifth actual r; fourth singleton
  T=sr(Rdet,0)
  G=can(Phi.resultant(T,1))
 else: # fourth and fifth on singleton profile
  print('two singleton front exact degrees',S0.degrees(),S1.degrees(),flush=True)
  YY=can(S0.resultant(S1,0))
  print('y projection',YY.degrees(),flush=True)
  G=can(Phi.resultant(YY,1))
 PG=coeff1(G,2);assert PG
 guards=[[B0(0),B0(1)],coeff1(D,2),[-R0,L]]
 if branch==4:guards.extend([[-R0,A],[-R0,B],coeff1(sr(term(H4,s),1),2)])
 PG=mon(guarded(PG,guards))
 print('exact nong front diagonal',front,slot,branch,len(PG)-1,flush=True)
 return PG
