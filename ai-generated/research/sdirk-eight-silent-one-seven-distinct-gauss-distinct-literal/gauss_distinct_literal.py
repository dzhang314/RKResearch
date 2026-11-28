"""Gauss hole r, distinct reverse root z on a literal silent front."""
from front_gauss_nonliteral import *
from gauss_tail_nonliteral import B0,cut_gamma,Pvar
from flint import fmpq_mpoly_ctx

CX=fmpq_mpoly_ctx.get(['u','g','r','t'])
u,g,r,t=CX.gens()
l4=lambda x:sum(v*x**i for i,v in enumerate(Lco))
LP=l4(r)/70;LT=t*t-CX.constant(Q(1)/2)
x=1-g;c=x-g*u
k=1+2*u-u*u
H=-2+u+4*u*u-u**3
J=4*u**3-12*u*u+3*u+2
p0=lambda X:70*X**3+(-140+70*r)*X**2+(90-140*r+70*r**2)*X-20+90*r-140*r**2+70*r**3

def C(F):return (F%LP)%LT
def div(F,V):
 a,b=divmod(F,V);assert not C(b)
 return C(a)
def divs(F,V):
 assert F
 while True:
  a,b=divmod(F,V)
  if C(b):return F
  F=C(a)

def E0(v):
 e=F2(v).v
 return e.a[0]+t*e.b[0]
def by_gu(F):
 R={}
 for (i,j,h,l),v in C(F).to_dict().items():
  assert l<=1 and h<=3
  a=E(Pvar([0]*h+[v]))
  if l:a=E(0,a.a)
  d=R.setdefault(i,{})
  d[j]=d.get(j,B0(0))+B0(a)
 return [trim([R.get(i,{}).get(j,B0(0)) for j in range(max(R.get(i,{}),default=-1)+1)])
            for i in range(max(R,default=-1)+1)]
def by_g(F):
 M=by_gu(F);assert len(M)<=1
 return M[0] if M else []

def at_gap(F,A,B):
 n=F.degrees()[0]
 return C(sum(v*A**i*B**(n-i)*g**j*r**h*t**l for (i,j,h,l),v in F.to_dict().items()))

@lru_cache(None)
def projection(f,i,mode,sole):
 A,B,m,ha,hb,a,b,hh,*_=frontdata(f,i)
 z=g*E0(a)
 xp,cp=x-z,c-z
 F9=div(C(p0(c)*xp-k*p0(x)*cp),u)
 d=x-g*(2-u if mode else 2*u)
 dp=d-z
 if mode is None:
  F8=C(2*xp+g*k*(u-2))
 elif mode:
  F8=div(C(p0(d)*xp-k*p0(x)*dp),u-2)
  F8=div(C(F8+F9),u-1)
 else:
  F8=divs(C(H*p0(d)*xp+k*J*p0(x)*dp),u)
 guards=[g,xp,p0(x),z-r]+([p0(z)] if sole else [])
 guards=list(map(by_g,guards))
 G=mon(guarded(by_g(C(F9.resultant(F8,0))),guards))
 PG=[]
 if mode is False:
  n=x-r;den=2*g
  A8=by_g(at_gap(F9,n,den));B8=by_g(at_gap(J,n,den))
  PG=mon(guarded(gcdp(A8,B8),guards))
 TWO=by_g(C(E0(ha)*p0(g*E0(B))-E0(hb)*p0(g*E0(A))))
 assert len(G)-1==({True:6,False:24,None:11}[mode])
 if mode is False:assert len(PG)==1 # A distinct reverse root forbids an active eighth hole.
 print('distinct Gauss literal projection:',f,i,mode,sole,len(G)-1,len(PG)-1,
       len(gcdp(G,TWO))-1, (len(gcdp(PG,TWO))-1) if PG else '-',
       flush=True)
 return G,PG,by_gu(F9),by_gu(F8),TWO

def fields2(f,i,mode,sole,p,t):
 G,PG,Ce,De,_=projection(f,i,mode,sole)
 for G0,n in split_degree(G,Ce):
  for F,g,r,lift in cut_gamma(G0,p,t):
   A=trim([ev(list(map(lift,v)),g) for v in Ce])
   B=[ev(list(map(lift,v)),g) for v in De]
   assert len(A)==n+1
   Z=gcdp(A,B)
   if len(Z)<=1:continue
   U=Tower(Z);u=U.gen()
   yield U,U(g),u,U(r)

def shared5(F,gg,r,a,b,s,h4,fd,Q,P):
 h,T0,A0,T1,A1=fterms(F,fd,a,s,h4)
 e1=h*ev(T0,b)*Q+ev(T1,b)*ev(P,b)
 e2=h*ev(A0,b)*Q+ev(A1,b)*ev(P,b)
 span_unit(F,e1,e2)
 return True

def phase2(f,i,mode,variant,p,t):
 # The silent root is at branch index i; the opposite front is active
 # only for the shared physical-clock branch.
 if variant=='sole':
  G,PG,_,_,TWO=projection(f,i,mode,True)
  assert len(gcdp(G,TWO))==1
  return True
 sole=variant=='neither'
 j=i if sole else 1-i
 fd=frontdata(f,j)
 assert len(gcdp(fd[8],exact_uc_y(fd[19])))==1
 n=0
 for F,g,u,r in fields2(f,i,mode,sole,p,t):
  n+=1
  g.inv()
  a,b,hh=map(F,fd[5:8])
  h4=list(map(F,fd[8]))
  P0=Pcoeff(F,r)
  PP=[g**k*v for k,v in enumerate(P0)]
  Q=ev(PP,a);P=sc(PP,hh)
  Phi,e=qr(add(sc(h4,Q),sc(P,-1)),[-a,F(1)])
  assert not e and len(Phi)==3
  Phi[-1].inv()
  W=Nested(mon(Phi));s=W.gen()
  hh4=list(map(W,h4));Qq=W(Q);Pp=list(map(W,P))
  assert test5(W,W(g),W(r),W(a),s,hh4,fd,Qq,Pp,6,0)
  if not sole and mode is not None:
   assert shared5(W,W(g),W(r),W(a),W(b),s,hh4,fd,Qq,Pp)
 assert n
 print('verified Gauss distinct literal:',f,i,mode,variant,p,n,flush=True)
 return True
