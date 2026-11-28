"""Retain and check actual fourth-leading-zero u roots, not all u at their γ."""
from leading_branch import *
from nofront_arith_cross import E_su
from pseudo_cut import Remainder,SplitE
from shared_arith_projection import syl,coefficients_e
from shared_silent8_projection import enorm

def exact_carrier(f,i):
 R,q0,q1,safe=tail(f,i)
 Phi,*_=front_polys(f,i)
 H=E_su(Phi)[-1];Q=coefficients_e(R);ell=Q[-1]
 T=syl(Q,H);assert T
 guards0=[ell]+[ef(Gcoeff(x)) for x in safe]
 B=e_sf(eguard(T,guards0))
 assert B.degree()==50
 C,D=guards(f,i)
 assert egcd(B,C).degree()==egcd(B,D).degree()==0
 return B,Q,H

def cond(C,R,H):
 P=Remainder(C)
 try:
  Y=P.trim(R);L=P.trim(H);assert Y
  D=P.gcd(Y,L) if L else Y
  assert len(D)>1
  # Keep the other u components explicitly; on them the same γ may have
  # ordinary, nonzero fourth leading coefficient.
  Z=Y
  if L:
   while len(Z)>1:
    J=P.gcd(Z,L)
    if len(J)<=1:break
    Z,r=P.pseudo_div(Z,J);assert not r and Z
  else:Z=[E(1)]
  return [(unef(C),list(map(unef,D)),len(Z)-1)]
 except SplitE as e:
  A=e.Q;B=eexact(C,A).monic()
  return cond(A,R,H)+cond(B,R,H)

@lru_cache(None)
def profiles(f,i):
 B,R,H=exact_carrier(f,i);W=[]
 for F,m in enorm(B).factor()[1]:
  F=egcd(B,E(F))
  if F.degree()>0:W+=cond(F,R,H)
 assert sum(len(C)-1 for C,_,_ in W)==50
 print('exact fourth-leading actual u versus retained other u:',
       f,i,[(len(A)-1,len(D)-1,n) for A,D,n in W],flush=True)
 return W

def check4(f,i,p,t):
 fd=frontdata(f,i);Phi,*_=front_polys(f,i);R,q0p,q1p,safe=tail(f,i)
 ph=[[unef(v) for v in a] for a in E_su(Phi)]
 q0c,q1c=map(Vcoeff,(q0p,q1p))
 n=0;fail=[]
 for J,W0,m in profiles(f,i):
  for G,gg in gammas(J,p,t):
   evg=lambda q:ev(list(map(G,q)),gg)
   r=trim([evg(a) for a in W0]);assert len(r)==len(W0)
   U=Tower(mon(r));u0=U.gen();g0=U(gg)
   evu=lambda p:ev([U(evg(w)) for w in p],u0)
   S=[evu(v) for v in ph]
   assert len(S)==4 and not S[-1]
   S=S[:-1];n+=1
   if not unit_b(U,S[-1]):
    fail.append((n,'further s degree'));continue
   W=Nested(sc(S,inverse_one(U,S[-1])));s0=W.gen()
   g0,u0=W(g0),W(u0)
   a,b,ha=map(W,fd[5:8]);H4=list(map(W,fd[8]))
   x=1-g0;c=x-g0*u0;d=x-2*g0*u0
   q0,q1=W(evu(q0c)),W(evu(q1c))
   L=list(map(W,Lco));La=ev(L,g0*a)
   Qp=[La*q0,La*g0*q1];Pp=[ha*(q0+q1*g0*a)*v*g0**j for j,v in enumerate(L)]
   h,T0,A0,T1,A1=fterms(W,fd,a,s0,H4)
   T=add(sc(mul(T0,Qp),h),mul(T1,Pp));A=add(sc(mul(A0,Qp),h),mul(A1,Pp))
   D=list(map(W,nodal([a,s0])))
   T,r=qr(T,D);assert not r
   A,r=qr(A,D);assert not r
   B=nodal_y5(W,g0,[x,c,d,g0*s0],q0,q1)
   if not test_unit(W,polyres(W,B,T,3,3),polyres(W,B,A,3,3),polyres(W,T,A,3,3)):
    fail.append((n,'fifth',str(G.M)))
 print('actual fourth-leading-zero phase',f,i,p,n,fail,flush=True)
 return fail

if __name__=='__main__':
 from itertools import product
 for f,i in product((True,False),(0,1)):check4(f,i,1103,161)
