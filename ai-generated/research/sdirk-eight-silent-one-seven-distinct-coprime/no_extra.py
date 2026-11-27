"""Both literal fronts, k!=0, coprime nonconstant Q, no separate reverse aggregate."""
from one_front_zero import *
from both_front_silent8 import context
from arithmetic_nonzero import guarded
from gauss_separate import span_unit
from unequal_finite import det3,moment
from off8_fibers import cramer
from flint import fmpq_mpoly_ctx

F2=ExField(E(P([0,1])))
cx=fmpq_mpoly_ctx.get(['y','u','g','t'])
y,u,g,t=cx.gens()
def cv(F,a):return F(Epoly(JJ(a))) if a else F(0)

def expr(a):
 a=F2(a).v
 return a.a[0]+t*a.b[0]
def term(ps,x):return sum(expr(v)*x**i for i,v in enumerate(ps))
def parts(F):
 R={}
 for (i,j,k,l),v in F.to_dict().items():
  a=R.setdefault((i,j,k),[Q(0),Q(0)]);a[l%2]+=v/2**(l//2)
 return {e:F2(E(P([a]),P([b]))) for e,(a,b) in R.items()}
def can(F):
 if isinstance(F,int):return cx.constant(F)
 return sum((expr(v)*y**i*u**j*g**k for (i,j,k),v in parts(F).items() if v),cx.constant(0))
def exdiv(F,H):
 T,R=divmod(F,H);T,R=can(T),can(R)
 assert not R
 return T
def evalg(F,M,gamma):
 X={}
 for (i,j,k),v in parts(M).items():
  X[i,j]=X.get((i,j),F(0))+F(v)*gamma**k
 return X
def coefficients(F,M,gamma,idx):
 X=evalg(F,M,gamma)
 d={}
 for pair,q in X.items():
  if not q:continue
  assert not pair[1-idx]
  d[pair[idx]]=q
 return [d.get(j,F(0)) for j in range(max(d,default=-1)+1)]
def gcoeff(M):
 d={}
 for (i,j,k),v in parts(M).items():
  if v:
   assert not i and not j
   d[k]=v
 return [d.get(j,F2(0)) for j in range(max(d,default=-1)+1)]

@lru_cache(None)
def phases(front):
 F=F2
 A,B,m=map(lambda r:cv(F,r),ends(front,1));ha,hb=(A-1)/2,(B-1-m)/2
 H4=list(map(lambda r:cv(F,r),pol(h4(front),lambda v:v)))
 sh,AA,e,QT,QA=context(F,A,B,m,ha,hb,None,H4)
 qA=[F(v)*A**i/ha for i,v in enumerate(Lco)]
 qB=[F(v)*B**i/hb for i,v in enumerate(Lco)]
 q1=sc(add(qB,sc(qA,-1)),1/(B-A))
 q0=add(qA,sc(q1,-A))
 J=-F(4)/3+2*(A+B)-2*A*B
 DT=[2-F(4)/3*(A+B)+2*A*B,J]
 DA=add([1-2*sh[0]-2*sh[1]],sc(e,J))
 # Physical row five with an unequal defect cannot share the pole of physical four.
 slopes=gcdp(add(DT,sc(QT,-1)),add(DA,sc(QA,-1)))
 slopes=guarded(slopes,[[-A,F(1)],[-B,F(1)]])
 assert len(slopes)==1
 return A,B,m,ha,hb,H4,qA,qB,q0,q1,sh,e,QT,QA,DT,DA

@lru_cache(None)
def projection_front(front):
 A,B,m,ha,hb,H4,qA,qB,q0,q1,sh,e,QT,QA,DT,DA=phases(front)
 q,z=term(q1,g),term(q0,g)
 Qa=z+q*y
 a,b=map(expr,(A,B))
 p=sum(v*(g*y)**i for i,v in enumerate(Lco))
 M0=y-1;M1=y*y/2-y;M2=y**3/3-y*y
 J=M2-(a+b)*M1+a*b*M0
 R0=q*(y**3-y**4/4+(a+b)*M2-a*b*M1)-z*J
 R1=q*(expr(sh[0])*M0+expr(sh[1])*M1)+(q*expr(e[0])-z*expr(e[1]))*J
 E0=can(R0*Qa+(q*(expr(DT[0])-term(QT,y))-z*expr(DT[1]))*p)
 E1=can(R1*Qa+(q*(expr(DA[0])-term(QA,y))-z*expr(DA[1]))*p)
 T,Q0=exdiv(exdiv(E0,y-a),y-b),exdiv(exdiv(E1,y-a),y-b)
 gg=gcoeff(can(T.resultant(Q0,0)));assert gg
 L=[F2(v) for v in Lco]
 pX=subst(L,[F2(1),F2(-1)])
 q0x=add(mul([F2(0),F2(1)],q0),mul([F2(1),F2(-1)],q1))
 pro=sum_poly([sc(mul(power(sc(mul([F2(0),F2(1)],q0),-1),i),power(q1,4-i)),v) for i,v in enumerate(L)])
 guards=[[F2(0),F2(1)],qA,qB,q1,pX,q0x,pro]
 M=mon(guarded(gg,guards))
 # Gap polynomial after the padded u factor; only its actual leading coefficient is needed for an exact split.
 xx=1-g;cc=xx-g*u;qq=lambda v:g*z+q*v
 L4=lambda x:sum(v*x**i for i,v in enumerate(Lco))
 K=1+2*u-u*u
 F9=exdiv(can(L4(cc)*qq(xx)**2-K*L4(xx)*qq(cc)**2),u)
 lc=gcoeff(sum((expr(v)*g**e for (i,j,e),v in parts(F9).items() if j==3 and not i),cx.constant(0)))
 assert lc
 G=gcdp(M,lc);N=mon(guarded(M,[lc]))
 print('coprime pole row-five projection',front,len(M)-1,'leading gap',len(G)-1,len(N)-1,flush=True)
 return M,T,Q0,F9,G,N

def g_parts(front,p,t):
 M,T,Q0,F9,G,N=projection_front(front)
 C=Bfield(nmod_poly([0,1],p),p,t)
 for J,flag in ((G,True),(N,False)):
  if len(J)<=1:continue
  Md=nmod_poly([int(C(a).x[0]) for a in J],p)
  assert Md.degree()==len(J)-1 and Md.leading_coefficient()==1
  for J0,_ in Md.factor()[1]:
   B=Bfield(J0,p,t);gamma=B(nmod_poly([0,1],p))
   R=coefficients(B,F9,gamma,1)
   if not R:raise ArithmeticError('identically zero gap polynomial')
   assert len(R)==(3 if flag else 4)
   U=Tower(mon(R));u0=U.gen()
   yield U,U(gamma),u0,T,Q0,flag

def mode(front,rear,p,t):
 exact=phases(front)
 for U,g,u,T,Q0,flag in g_parts(front,p,t):
  A,B,m,ha,hb=map(U,exact[:5]);H4,qA,qB,q0,q1,sh,e,QT,QA,DT,DA=[list(map(U,v)) for v in exact[5:]]
  a,b=ev(q0,g),ev(q1,g);b.inv()
  x=1-g;cc=x-g*u;dd=x-g*(2-u if rear else 2*u)
  Z=-a/b
  k=1+2*u-u*u
  L=list(map(U,Lco))
  qx,qc,qd=[g*a+b*v for v in (x,cc,dd)]
  px,pc,pd=[ev(L,v) for v in (x,cc,dd)]
  if rear is None:
   e0=qx+g*b*k*(u-2)/2
   if conditional_zero(U,e0):continue
   pts=[g*A,g*B,x,cc]
   M=moment(U,pts,[g*a,b],6)
   H=[[M[i+j] for j in range(3)] for i in range(3)]
   D=det(H);D.inv()
   N=[r/(D*g**(3-i)) for i,r in enumerate(cramer(H,[-M[3],-M[4],-M[5]]))]+[U(1)]
   # After the pure gauge, the remaining first literal row is active.
   span_unit(U,e0,multicol(N,coefficients(U,T,g,0)),multicol(N,coefficients(U,Q0,g,0)))
  else:
   if rear:e0=pd*qx*qx-k*px*qd*qd
   else:
    h=-2+u+4*u*u-u**3;d=4*u**3-12*u*u+3*u+2
    e0=h*pd*qx*qx+k*d*px*qd*qd
   if conditional_zero(U,e0):continue
   D=moment(U,[g*A,g*B,x,cc,dd],[g*a,b],5)
   span_unit(U,e0,det3(D))
 return True
