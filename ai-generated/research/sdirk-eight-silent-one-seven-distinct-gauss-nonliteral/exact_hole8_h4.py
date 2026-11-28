"""Remove only exact H4=0 literal factors in the arithmetic-eighth Gauss case."""
from gauss_small_nonliteral import *
from gauss_tail_nonliteral import B0
from silent_guard import ExactField,SplitAt

class GaussExact(ExactField):
 def __init__(self,G):self.F,self.B=G,B0

def a0(v):return B0(F2(v).v)

def capped_phi(f,i,F,g,r):
 fd=frontdata(f,i)
 a,b,ha=map(lambda v:F(a0(v)),fd[5:8])
 H4=list(map(lambda v:F(a0(v)),fd[8]))
 P0=[g**j*q for j,q in enumerate(Pcoeff(F,r))]
 Q,P=ev(P0,a),sc(P0,ha)
 P4,e=qr(add(sc(H4,Q),sc(P,-1)),[-a,F(1)]);assert not e
 return P4,H4

def allowed(f,i,G):
 X=GaussExact(G);u=X.gen();r=X(B0(E(P([0,1]))))
 try:
  g=(1-r)/(1+2*u)
  M,H=capped_phi(f,i,X,g,r)
  old=len(M)-1
  while True:
   A=gcdp(M,H)
   if len(A)<=1:break
   M,e=qr(M,A);assert not e
  assert M
  return [(G,[list(v.x) for v in mon(M)],old)]
 except SplitAt as e:
  A=mon(e.d);B,rem=qr(G,A);assert not rem
  return allowed(f,i,A)+allowed(f,i,B)

def verify(f,i,p,t):
 fd=frontdata(f,i)
 assert len(gcdp(fd[8],exact_uc_y(fd[19])))==1
 for G,YY,old in allowed(f,i,mon(list(map(B0,[2,3,-12,4])))):
  assert (old,len(YY)-1)==(2,1 if f else 2)
  print('hole8 exact H4 degrees',f,i,len(G)-1,old,len(YY)-1,flush=True)
  for B,r in basefields(p,t):
   R=nmod_poly([int(B(a).x[0]) for a in G],p)
   assert R.degree()==len(G)-1 and R.leading_coefficient()==1
   for M,_ in R.factor()[1]:
    F=Bfield(M,p,t);u=F(nmod_poly([0,1],p));r0=F(int(r.x[0]))
    g=(1-r0)/(1+2*u)
    Y=trim([ev([F(int(B(v).x[0])) for v in a],u) for a in YY])
    assert len(Y)==len(YY) and Y[-1]==1
    if len(Y)==1:continue
    S=Tower(Y);s=S.gen()
    a,b,ha=map(S,fd[5:8]);H4=list(map(S,fd[8]))
    Qp=[S(g)**j*q for j,q in enumerate(Pcoeff(S,S(r0)))]
    Q,P=ev(Qp,a),sc(Qp,ha)
    assert test5(S,S(g),S(r0),a,s,H4,fd,Q,P,6,8)
 return True
