"""Actual placement and signed moments for constant Q with nonliteral reverse root."""
from constant_front_projection import *
from front_tail_close import split_deg,test_unit,hom
from front_gauss_nonliteral import fterms
from constant_literal_reverse import cmoments,moment_const
from silent_guard import ExactField,SplitAt

class ConstExact(ExactField):
 def __init__(self,G):self.F,self.B=G,F2

def exact_allowed(G,PH,H4):
 X=ConstExact(G);g=X.gen()
 try:
  P=trim([ev(list(map(X,w)),g) for w in PH]);assert P
  h=list(map(X,H4));deg=len(P)-1
  while True:
   A=gcdp(P,h)
   if len(A)<=1:break
   P,e=qr(P,A);assert not e
  assert P
  return [(G,[list(v.x) for v in mon(P)],deg)]
 except SplitAt as e:
  A=mon(e.d);B,rem=qr(G,A);assert not rem
  return exact_allowed(A,PH,H4)+exact_allowed(B,PH,H4)

@lru_cache(None)
def g_and_s(f,i):
 N,Phi,FT,FA=project(f,i)
 fd=frontdata(f,i);hh=fd[8];a=E0(fd[5])
 G=mon(guarded(N,[bg(C(L4(1-g))),bg(C(1-g-g*a))]))
 bad=bg(C(term0(hh,s).resultant(L4(g*s),1)))
 I=gcdp(G,bad);J=mon(guarded(G,[bad]));PH=bsg(Phi)
 spec=exact_allowed(squarefree(I),PH,hh) if len(I)>1 else []
 assert (len(G)-1,len(I)-1,len(J)-1)==(100,12,64)
 assert [(len(v)-1,len(f)-1,j) for v,f,j in spec]==[(12,2,3)]
 print('constant exact fourth splits',f,i,len(G)-1,len(I)-1,len(J)-1,
       [(len(D)-1,len(PH)-1,j) for D,PH,j in spec],flush=True)
 return spec+([(J,PH,3)] if len(J)>1 else [])

CV=fmpq_mpoly_ctx.get(['u','g'])
uu,gg=CV.gens()
x=1-gg;c=x-gg*uu
k=1+2*uu-uu*uu
H=-2+uu+4*uu**2-uu**3
T=4*uu**3-12*uu**2+3*uu+2

def div0(P,D):
 R,S=divmod(P,D);assert not S
 return R

@lru_cache(None)
def tails(mode):
 if mode=='star':
  d=x-gg*(2-uu)
  F=div0((2-uu)*L4(c)-uu*L4(d)+k*(2*uu-2)*L4(x),uu*(uu-1)*(uu-2))
 elif mode=='arith':
  d=x-2*gg*uu
  F=H*L4(d)+2*T*L4(c)-k*T*L4(x)
  while True:
   R,S=divmod(F,uu)
   if S:break
   F=R
 else:
  assert mode=='silent'
  F=div0((uu-2)*L4(c)-(2*uu+k*(uu-2))*L4(x),uu)
 D={}
 for (i,j),v in F.to_dict().items():D.setdefault(i,{})[j]=F2(E(v))
 R=[trim([D.get(i,{}).get(j,F2(0)) for j in range(max(D.get(i,{}),default=-1)+1)])
        for i in range(max(D,default=-1)+1)]
 assert len(R)-1=={'star':2,'arith':5,'silent':4}[mode]
 print('constant root-eliminated gap',mode,len(R)-1,flush=True)
 return R

def gammas(M,p,t):
 B=Bfield(nmod_poly([0,1],p),p,t)
 Md=nmod_poly([int(B(v).x[0]) for v in M],p)
 assert Md.degree()==len(M)-1 and Md.leading_coefficient()==1
 for F,_ in Md.factor()[1]:
  W=Bfield(F,p,t);g=W(nmod_poly([0,1],p))
  yield W,g

def whole_field(f,i,mode,p,t):
 tail=tails(mode)
 for G,SH,j in g_and_s(f,i):
  if len(SH)==1:
   assert SH==[[F2(1)]]
   continue
  for D,k in split_deg(G,tail):
   for F,g in gammas(D,p,t):
    sy=trim([ev(list(map(F,v)),g) for v in SH])
    ut=trim([ev(list(map(F,v)),g) for v in tail])
    assert len(sy)==len(SH) and len(ut)==k+1
    if len(ut)<=1:continue
    U=Tower(mon(ut));u=U.gen()
    W=Nested(mon(list(map(U,sy))));s=W.gen()
    yield W,W(g),W(u),s

def one(f,i,mode,p,t):
 fd=frontdata(f,i);assert len(gcdp(fd[8],exact_uc_y(fd[19])))==1
 n=0
 for F,g,u,s in whole_field(f,i,mode,p,t):
  n+=1
  a,b,ha=map(F,fd[5:8]);H4=list(map(F,fd[8]))
  pp=list(map(F,Lco));P=[ha*v*g**j for j,v in enumerate(pp)];Q=ev(pp,g*a)
  h,T0,A0,T1,A1=fterms(F,fd,a,s,H4)
  A=add(sc(T0,h*Q),mul(T1,P));B=add(sc(A0,h*Q),mul(A1,P))
  D0=list(map(F,nodal([a,s])))
  A,e=qr(A,D0);assert not e
  B,e=qr(B,D0);assert not e
  E=polyres(F,A,B,3,3)
  X=1-g;C=X-g*u
  if mode=='silent':
   M,H=cmoments(F,g,[g*a,X,C,g*s],3)
   assert test_unit(F,E,polyres(F,M,A,3,3),polyres(F,M,B,3,3)),(n,'silent8')
   continue
  D=X-g*(2-u if mode=='star' else 2*u)
  Xp,Cp=ev(pp,X),ev(pp,C)
  k=1+2*u-u*u
  zn,zd=X*Cp-k*C*Xp,Cp-k*Xp
  J4=g*zd*s-zn
  pegs=[g*a,X,C,D]
  M,H=cmoments(F,g,pegs,3)
  assert test_unit(F,J4,E,polyres(F,M,A,3,3),polyres(F,M,B,3,3)),(n,'j4')
  D2=moment_const(F,pegs+[g*s],5)
  D3=det([[D2[i+j] for j in range(3)] for i in range(3)])
  assert test_unit(F,D3,hom(F,A,zn,g*zd,3),hom(F,B,zn,g*zd,3)),(n,'j5')
  M2,H2=cmoments(F,g,pegs+[g*s],2)
  assert test_unit(F,D3,E,polyres(F,M2,A,2,3),polyres(F,M2,B,2,3)),(n,'j67')
 assert n
 print('verified constant nonliteral tail:',f,i,mode,p,n,flush=True)
 return True
