"""One literal active front, other not at the singleton terminal x, k=0."""
from literal_terminal import *
from both_front_silent8 import context
from flint import fmpq_mpoly_ctx
CX=fmpq_mpoly_ctx.get(['y','s','g','t']);y,s,g,t=CX.gens()

def expr(q):
 q=F2(q).v
 return q.a[0]+t*q.b[0]
def term(a,w):return sum(expr(v)*w**i for i,v in enumerate(a))
def parts(M):
 L={}
 for (i,j,k,l),v in M.to_dict().items():
  a=L.setdefault((i,j,k),[Q(0),Q(0)]);a[l%2]+=v/2**(l//2)
 return {key:F2(E(P([a]),P([b]))) for key,(a,b) in L.items()}
def can(X):
 if isinstance(X,int):return CX.constant(X)
 return sum((expr(v)*y**i*s**j*g**k for (i,j,k),v in parts(X).items() if v),CX.constant(0))
def exact_g(X):
 Z={}
 for (i,j,k),v in parts(X).items():
  if v:
   assert not i and not j
   Z[k]=v
 return [Z.get(i,F2(0)) for i in range(max(Z,default=-1)+1)]
def exdiv(M,D):
 Q,R=divmod(M,D);return can(Q),can(R)
def ats(M):
 return can(sum((expr(v)*s**(i+j)*g**k for (i,j,k),v in parts(M).items() if v),CX.constant(0)))

@lru_cache(None)
def tail_profile(f,slot,rear,ori):
 F=F2
 A,B,m=map(lambda q:cv(F,q),ends(f,1))
 C,D,j=map(lambda q:cv(F,q),ends(True if rear is None else rear,ori))
 ha,hb=(A-1)/2,(B-1-m)/2
 anc,off,hh=(A,B,ha) if slot==0 else (B,A,hb)
 al,bl,af,of=map(expr,(A,B,anc,off));u=C-1
 x=1-g;c=1-g*expr(C);d=1-g*expr(D);a=g*af
 L4=lambda w:sum(v*w**i for i,v in enumerate(Lco))
 if rear is None:k,l,p0,p1=L4(c),-2*expr(u*u)*L4(x),x,c
 else:k,l,p0,p1=expr(u)*L4(d),-expr(D-1-j)*L4(c),c,d
 Bq=can(k+l);Aq=can(k*p0+l*p1)
 qf=lambda X:Aq-Bq*X
 den=can(L4(a));nu=can(expr(hh)*qf(a))
 Qp=lambda Y:can(den*qf(g*Y))
 Pn=lambda Y:can(nu*L4(g*Y))
 QpY,PnY=Qp(y),Pn(y)
 HH=[g,den,nu,1-g-g*of, x-a,c-a,L4(x),L4(c),qf(x),qf(c)]
 if rear is not None:HH.extend([d-a,L4(d),qf(d)])
 simple=[exact_g(can(v)) for v in HH]
 sh=exact_g(can(sum(v*Aq**i*Bq**(4-i) for i,v in enumerate(Lco))))
 return (A,B,m,C,D,ha,hb,anc,off,hh,exact_g(Aq),exact_g(Bq),exact_g(den),exact_g(nu),
         QpY,PnY,simple,sh)

@lru_cache(None)
def eqs(f,slot,rear,ori):
 A,B,m,C,D,ha,hb,anc,off,hh,Aq,Bq,Dn,Nn,Qp,Pn,guards,sh=tail_profile(f,slot,rear,ori)
 F=F2;al,bl,af=map(expr,(A,B,anc))
 H4=list(map(lambda u:cv(F,u),pol(h4(f),lambda z:z)))
 L0,AA,e,QT,QA=context(F,A,B,m,ha,hb,None,H4)
 tv,av=ev(QT,anc),ev(QA,anc)
 Hs=term(H4,s)
 s0=s-1-2*Hs;s1=s*s/2-s-2*Hs
 ta=(bl*s0-s1)*expr((B-A).inv());tb=s0-ta
 row_T=can(s**3-s**4/4+2*Hs+ta*al**3+tb*bl**3)
 row_A=can(Hs+ta*expr(ha)+tb*expr(hb))
 assert len(gcdp(H4,[v for j,v in enumerate(exact_sc(row_A,1))]))==1
 XT,rr=exdiv(can(row_T-expr(tv)*Hs),s-af);assert not rr
 XA,rr=exdiv(can(row_A-expr(av)*Hs),s-af);assert not rr
 m0=y-1;m1=y*y/2-y;m2=y**3/3-y*y
 J0=m2-(al+bl)*m1+al*bl*m0
 T0=y**3-y**4/4+(al+bl)*m2-al*bl*m1+s*J0
 A0=expr(L0[0])*m0+expr(L0[1])*m1+term(e,s)*J0
 JH=-F(4)/3+2*(A+B)-2*A*B
 DT=term([2-F(4)/3*(A+B)+2*A*B,JH],s)
 DA=expr(1-2*L0[0]-2*L0[1])+term(e,s)*expr(JH)
 T1=can(Hs*(DT-expr(tv))-XT*(y-af))
 A1=can(Hs*(DA-expr(av))-XA*(y-af))
 Et=can(Hs*T0*Qp+T1*Pn);Ea=can(Hs*A0*Qp+A1*Pn)
 Et,rr=exdiv(Et,y-af);assert not rr
 Ea,rr=exdiv(Ea,y-af);assert not rr
 Phi,R=exdiv(can(ats(Qp)*Hs-ats(Pn)),s-af);assert not R
 A,C0=exdiv(Et,y-s);B,C1=exdiv(Ea,y-s)
 assert not can(C0-ats(T0)*Phi) and not can(C1-ats(A0)*Phi)
 return Phi,A,B,Et,Ea,T0,A0,T1,A1,H4

def exact_sc(M,which):
 z={}
 for (i,j,k),v in parts(M).items():
  if v:
   ex=[i,j,k];assert not any(ex[m] for m in range(3) if m!=which)
   z[ex[which]]=v
 return [z.get(j,F2(0)) for j in range(max(z,default=-1)+1)]
