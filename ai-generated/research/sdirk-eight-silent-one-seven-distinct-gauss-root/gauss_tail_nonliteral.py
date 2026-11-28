"""Gauss hole r is the reverse root, without literal-clock hypothesis."""
from literal_shared_pole_late import *
from variable_gamma import Lf,G as Gvar
from one_front_zero import Pcoeff
from flint import fmpq_mpoly_ctx

R0=Epoly(Lf(Gvar).monic())
B0=ExField(R0)
RX=fmpq_mpoly_ctx.get(['u','g','r'])
uX,gX,rX=RX.gens()
L4=lambda X:sum(v*X**i for i,v in enumerate(Lco))
LP=L4(rX)/70
K=1+2*uX-uX*uX
H=-2+uX+4*uX*uX-uX**3
J=4*uX**3-12*uX*uX+3*uX+2
aX=1-gX
bX=aX-gX*uX
dX=lambda mode:aX-gX*(2-uX if mode else 2*uX)
p0=lambda X:70*X**3+(-140+70*rX)*X**2+(90-140*rX+70*rX**2)*X-20+90*rX-140*rX**2+70*rX**3

def remR(F):
 return F%LP

def divX(F,Q):
 x,y=divmod(F,Q)
 assert not remR(y)
 return remR(x)

def all_div(F,Q):
 assert F
 while True:
  x,y=divmod(F,Q)
  if remR(y):return F
  F=remR(x)

def by_g_u(F):
 M={}
 for (i,j,k),v in remR(F).to_dict().items():
  d=M.setdefault(i,{});d[j]=d.get(j,B0(0))+B0(E(P([0]*k+[v])))
 return [trim([M.get(i,{}).get(j,B0(0)) for j in range(max(M.get(i,{}),default=-1)+1)])
           for i in range(max(M,default=-1)+1)]
def by_g(F):
 Z=by_g_u(F)
 assert len(Z)<=1
 return Z[0] if Z else []

def substit_gap(P,A,B):
 n=P.degrees()[0]
 return remR(sum(v*A**i*B**(n-i)*gX**j*rX**k for (i,j,k),v in P.to_dict().items()))
def substit_g(P,G):
 return remR(sum(v*uX**i*G**j*rX**k for (i,j,k),v in P.to_dict().items()))

def nogamma(F,gg):
 assert gg.A is B0 if hasattr(gg,'A') else gg.ctx is B0
 return [ev(v,gg) for v in by_g_u(F)]

@lru_cache(None)
def tails0(mode):
 d=dX(mode)
 px,pc,pd=list(map(p0,(aX,bX,d)))
 X,C,D=aX-rX,bX-rX,d-rX
 f9=divX(remR(pc*X-K*px*C),uX)
 if mode is None:
  f8=remR(2*X+gX*K*(uX-2))
  fd=f8
 elif mode:
  fd=remR(pd*X-K*px*D)
  f8=divX(fd,uX-2)
  f8=divX(remR(f8+f9),uX-1)
 else:
  fd=remR(H*pd*X+K*J*px*D)
  f8=all_div(fd,uX)
 # Exact guards justify excluding actual diagonal zero and terminal defect/clock zero.
 GG=mon(guarded(by_g(remR(f9.resultant(f8,0))),list(map(by_g,[gX,X,px]))))
 assert GG
 G9=mon(guarded(by_g(substit_gap(fd,X,gX)),list(map(by_g,[gX,X,px]))))
 if mode is None:G8=[]
 else:G8=mon(guarded(by_g(substit_gap(f9,2*gX-X if mode else X,gX if mode else 2*gX)),list(map(by_g,[gX,X,px]))))
 assert (len(GG)-1,len(G9)-1,len(G8)-1)==({True:(6,6,5),False:(21,8,5),None:(11,3,-1)}[mode])
 print('exact nonliteral Gauss tail projections',mode,len(GG)-1,len(G9)-1,len(G8)-1,flush=True)
 return GG,G9,G8,by_g_u(f9),by_g_u(f8)

@lru_cache(None)
def x_hole(mode):
 if mode is None:return [B0(-2),B0(1)]
 d=dX(mode)
 P,C=p0(d),bX-rX
 Q,D=p0(bX),d-rX
 T= P*C-Q*D if mode else H*P*C+J*Q*D
 R=mon(guarded(nogamma(T,B0(1)-B0(E(Pvar([0,1])))),[[B0(0),B0(1)]]))
 assert len(R)-1==(3 if mode else 5)
 print('terminal hole exact gap',mode,len(R)-1,flush=True)
 return R
Pvar=P

def basefields(p,t):
 S=Bfield(nmod_poly([0,1],p),p,t)
 M=S.cast(R0)
 assert M.degree()==4 and M.leading_coefficient()==1
 fac=M.factor()[1]
 assert len(fac)==4 and all(C.degree()==1 and e==1 for C,e in fac)
 for C,e in fac:
  B=Bfield(C,p,t)
  r=B(nmod_poly([0,1],p))
  yield B,r

def cut_gamma(M,p,t):
 if len(M)<=1:return
 M=mon(M)
 for B,r in basefields(p,t):
  assert B.M.degree()==1
  Md=nmod_poly([int(B(v).x[0]) for v in M],p)
  assert Md.degree()==len(M)-1 and Md.leading_coefficient()==1
  for A,_ in Md.factor()[1]:
   F=Bfield(A,p,t);g=F(nmod_poly([0,1],p))
   rF=F(int(r.x[0]))
   def lift(v):return F(int(B(v).x[0]))
   yield F,g,rF,lift

# All finite exact gamma/actual u branches. Cases 9/8 supply rational gaps;
# x hole uses its own exact univariate equation after fixing gamma.
def fields(mode,hit,p,t):
 G,G9,G8,C0,D0=tails0(mode)
 if hit==0:
  for G0,n in split_degree(G,C0):
   for F,g,r,lift in cut_gamma(G0,p,t):
    C=trim([ev(list(map(lift,v)),g) for v in C0])
    D=[ev(list(map(lift,v)),g) for v in D0]
    assert len(C)==n+1
    Q=gcdp(C,D)
    if len(Q)<=1:continue
    U=Tower(Q);v=U.gen()
    yield U,U(g),v,U(r)
 elif hit==10:
  M=x_hole(mode)
  for B,r in basefields(p,t):
   X=list(map(B,M))
   assert len(trim(X))==len(M) and X[-1]==1
   U=Tower(X);v=U.gen()
   yield U,1-U(r),v,U(r)
 elif hit in (8,9):
  M=G9 if hit==9 else G8
  for F,g,r,lift in cut_gamma(M,p,t):
   g.inv()
   v=(1-g-r)/g
   if hit==8:v=2-v if mode else v/2
   yield F,g,v,r
