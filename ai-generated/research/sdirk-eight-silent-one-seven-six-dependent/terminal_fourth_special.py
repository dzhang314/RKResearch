"""Dependent terminal double: unknown fourth clock, active or physically silent."""
from one_front_zero import *
from both_front_silent8 import context
from equal_detected import det3
from arithmetic_nonzero import guarded
from gauss_separate import span_unit
from flint import fmpq_mpoly_ctx

F2=ExField(E(P([0,1])))
Cv=fmpq_mpoly_ctx.get(['y','s','t']);y,s,t=Cv.gens()
def ff(q):return F2(Epoly(JJ(q))) if q else F2(0)
def expr(q):
 q=F2(q).v
 return q.a[0]+t*q.b[0]
def term(pp,x):return sum(expr(q)*x**j for j,q in enumerate(pp))
def parts(P0):
 V={}
 for (i,j,k),v in P0.to_dict().items():
  L=V.setdefault((i,j),[Q(0),Q(0)]);L[k%2]+=v/2**(k//2)
 return {key:F2(E(P([a]),P([b]))) for key,(a,b) in V.items()}
def can(W):
 return sum((expr(v)*y**i*s**j for (i,j),v in parts(W).items() if v),Cv.constant(0))
def coeff_y(W):
 V=parts(W);A=[]
 for i in range(max((i for i,j in V),default=-1)+1):
  A.append(trim([V.get((i,j),F2(0)) for j in range(max((j for n,j in V if n==i),default=-1)+1)]))
 return A
def poly_s(W):
 G=coeff_y(W);assert len(G)==1
 return G[0]
def exdiv(W,X):
 T,E=divmod(W,X);T,E=can(T),can(E);assert not E
 return T

@lru_cache(None)
def normalized(front):
 F=F2
 A,B,m=map(ff,ends(front,1));ha,hb=(A-1)/2,(B-1-m)/2
 H4=list(map(ff,pol(h4(front),lambda v:v)))
 S,AA,e,QT,QA=context(F,A,B,m,ha,hb,None,H4)
 a,b=map(expr,(A,B));H=term(H4,s)
 m0=s-1-2*H;m1=s*s/2-s-2*H
 wa=(b*m0-m1)*expr((B-A).inv());wb=m0-wa
 T4=can(s**3-s**4/4+2*H+wa*a**3+wb*b**3)
 A4=can(H+wa*expr(ha)+wb*expr(hb))
 X=can(T4-H*term(QT,s));Y=can(A4-H*term(QA,s))
 XT=exdiv(exdiv(X,s-a),s-b);XA=exdiv(exdiv(Y,s-a),s-b)
 assert len(gcdp(poly_s(XT),poly_s(XA)))==1
 n0=y-1;n1=y*y/2-y;n2=y**3/3-y*y
 J=n2-(a+b)*n1+a*b*n0
 T5=can(y**3-y**4/4+(a+b)*n2-a*b*n1+s*J)
 A5=can(expr(S[0])*n0+expr(S[1])*n1+term(e,s)*J)
 return A,B,ha,hb,H4,XT,XA,T5,A5

@lru_cache(None)
def polars(front,which):
 A,B,ha,hb,H4,XT,XA,T5,A5=normalized(front)
 a,b=map(expr,(A,B));H=term(H4,s)
 def L(Y):
  if which is None:return sum(v*Y**i*(1+s)**(4-i) for i,v in enumerate(Lco))
  g=expr(1/(1+(A if which==0 else B)))
  return sum(v*g**i*Y**i for i,v in enumerate(Lco))
 qa=L(a)*expr(1/ha);qb=L(b)*expr(1/hb)
 LQ=can(qa+(s-a)*(qb-qa)*expr((B-A).inv()))
 XL=exdiv(exdiv(can(L(s)-H*LQ),s-a),s-b)
 E=can(L(y)*XT-T5*XL);G=can(L(y)*XA-A5*XL)
 R=can(E.resultant(G,0))
 Hh=[[-A,F2(1)],[-B,F2(1)]]
 if which is None:Hh.extend(([F2(1),F2(1)],H4))
 M=poly_s(R)
 if any(not q for q in Hh):raise Exception('unexpected guard')
 exc=mon(guarded(poly_s(XL),Hh))
 M=mon(guarded(M,[*Hh,poly_s(XL)]))
 E1,E2=map(coeff_y,(E,G))
 print('special fourth projections',front,which,len(exc)-1,len(M)-1,
       'leading singular degrees',len(gcdp(M,E1[-1]))-1,len(gcdp(M,E2[-1]))-1,flush=True)
 return exc,M,E1,E2,coeff_y(T5),coeff_y(A5),coeff_y(can(L(y)))

def candidates(front,which,p,t):
 exc,M,E,G,T,A,L=polars(front,which)
 V=Bfield(nmod_poly([0,1],p),p,t)
 for Y,fam in ((exc,True),(M,False)):
  if len(Y)<=1:continue
  pol=[V(v) for v in Y];assert pol[-1]==1
  # Over the exact quadratic coefficient field, every factor is covered.
  mp=nmod_poly([int(q.x[0]) for q in pol],p)
  assert mp.degree()==len(Y)-1 and mp.leading_coefficient()==1
  for fac,_ in mp.factor()[1]:
   W=Bfield(fac,p,t);s=W(nmod_poly([0,1],p))
   j=lambda a:trim([ev(list(map(W,x)),s) for x in a])
   if fam:
    QQ=j(L);assert len(QQ)==5
    U=Tower(mon(QQ));v=U.gen()
    span_unit(U,ev(list(map(U,j(T))),v),ev(list(map(U,j(A))),v))
    continue
   EE,GG=j(E),j(G)
   for U0,W0 in [(EE,GG),(GG,EE)]+[(add(EE,sc(GG,i)),GG) for i in range(1,5)]:
    if len(U0)!=5:continue
    try:PP=mon(U0)
    except ArithmeticError:continue
    U=Tower(PP);yr=U.gen()
    yield U,U(s),yr,ev(list(map(U,W0)),yr)
    break
   else:raise ArithmeticError('unpreserved leading fifth degree')

def verify(front,which,rear,ori,p,t):
 for F,s,y,e in candidates(front,which,p,t):
  cv=lambda a:F(Epoly(JJ(a))) if a else F(0)
  A,B,_=map(cv,ends(front,1));a,b,_=map(cv,ends(rear,ori))
  g=1/(1+(s if which is None else (A if which==0 else B)))
  D=nodal([1-g*a,1-g*b,g*y]);M=[intp(F,D,j) for j in range(5)]
  span_unit(F,e,det3(M))
 return True
