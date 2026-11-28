"""Exact fixed literal fifth geometry and affine triple-read projection."""
from shared_fifth_reads import *
from constant_front_tail import ConstExact
from literal_shared_pole_late import polyres,squarefree
from front_tail_close import test_unit
from silent_guard import SplitAt

def sexact(N,guards):
 for h in guards:
  if not h:continue
  while len(N)>1:
   D=gcdp(N,h)
   if len(D)<=1:break
   N,e=qr(N,D);assert not e
 return mon(N)

def exact_gamma(f,i,M,sel):
 X=ConstExact(M);s=X.gen()
 fd=frontdata(f,i)
 A,B,m,ha,hb,a,b,hh=map(X,fd[:8]);H4=ev(list(map(X,fd[8])),s)
 G,dat=read(f,i)
 C0,C1,D0,D1=[ev(list(map(X,p)),s) for p in dat]
 try:
  h=-H4*(C0 if sel==0 else C1)/(D0 if sel==0 else D1)
  h.inv();(s-a).inv();(s-b).inv();H4.inv()
  p=lambda c:[X(v)*c**j for j,v in enumerate(Lco)]
  la,lb,ls=map(p,(a,b,s))
  Y=sum_poly([sc(la,(s-b)/hh),sc(ls,(b-a)/H4),sc(lb,(a-s)/h)])
  assert Y
  guards=[[X(0),X(1)],la,lb,ls,[X(1),-1-a],[X(1),-1-b],[X(1),-1-s]]
  V=sexact(Y,guards)
  return [(M,[list(v.x) for v in V],sel)]
 except SplitAt as e:
  N=mon(e.d);R,e=qr(M,N);assert not e
  return exact_gamma(f,i,N,sel)+exact_gamma(f,i,R,sel)

@lru_cache(None)
def projections(f,i):
 G,(T0,A0,T1,A1)=read(f,i)
 G=squarefree(G)
 R=gcdp(G,T1);Q=mon(guarded(G,[T1]))
 V=[]
 for J,j in ((Q,0),(R,1)):
  if len(J)>1:V+=exact_gamma(f,i,J,j)
 assert [(len(J)-1,len(G)-1,j) for J,G,j in V]==[(1 if f else 3,4,0)]
 print('shared fifth exact s/gamma branches:',f,i,[(len(J)-1,len(G)-1,j) for J,G,j in V],flush=True)
 return V

def fields(f,i,p,t):
 Z=Bfield(nmod_poly([0,1],p),p,t)
 for J,V,sel in projections(f,i):
  M=nmod_poly([int(Z(v).x[0]) for v in J],p)
  assert M.degree()==len(J)-1 and M.leading_coefficient()==1
  for W,_ in M.factor()[1]:
   S=Bfield(W,p,t);s=S(nmod_poly([0,1],p))
   G=[ev(list(map(S,v)),s) for v in V]
   assert G[-1]==1
   if len(G)<=1:continue
   F=Tower(G);g=F.gen()
   yield F,g,F(s)

def tail_polys(F,g,s,a,b,ha,H4,star):
 X=1-g;x=X/g
 L=list(map(F,Lco))
 a0=ev(L,g*a)/ha;s0=ev(L,g*s)/H4
 q1=(s0-a0)/(s-a);q0=a0-a*q1
 Qx=q0+q1*x
 px=ev(L,X);z=g*b
 c=[X,-g];d=[X-2*g,g] if star else [X,-2*g]
 Pc,Pd=subst(L,c),subst(L,d)
 Qc=[Qx,-q1];Qd=[Qx-2*q1,q1] if star else [Qx,-2*q1]
 k=[F(1),F(2),F(-1)]
 F9=add(sc(Pc,(X-z)*Qx),sc(mul(mul(k,add(c,[-z])),Qc),-px))
 assert F9[0]==0
 F9=F9[1:]
 if star:
  F8=add(sc(Pd,(X-z)*Qx),sc(mul(mul(k,add(d,[-z])),Qd),-px))
  F8,e=qr(F8,[F(-2),F(1)]);assert not e
  F8,e=qr(add(F8,F9),[F(-1),F(1)]);assert not e
 else:
  H=list(map(F,[-2,1,4,-1]));T=list(map(F,[2,3,-12,4]))
  F8=add(sc(mul(H,Pd),(X-z)*Qx),sc(mul(mul(mul(k,T),add(d,[-z])),Qd),px))
  assert not F8[0]
  F8=F8[1:]
 return F9,F8,q0,q1

def verify(f,i,star,p,t):
 fd=frontdata(f,i);n=0
 for F,g,s in fields(f,i,p,t):
  a,b,ha=map(F,fd[5:8]);H4=ev(list(map(F,fd[8])),s);n+=1
  A,B,q0,q1=tail_polys(F,g,s,a,b,ha,H4,star)
  R=polyres(F,A,B,3,2 if star else 6)
  assert test_unit(F,R),(n,len(A)-1,len(B)-1)
 assert n
 print('verified shared fifth direct tail:',f,i,star,p,n,flush=True)
 return True
