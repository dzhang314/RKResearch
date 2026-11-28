"""Actual row four/five signed missing cubic for the no-active-literal star chart."""
from nofront_star_front import *
from constant_front_tail import gammas,exact_allowed
from front_tail_close import test_unit
from front_gauss_nonliteral import fterms
from shared_star_checks import mmask,cmask
from shared_silent8_projection import egcd
from shared_silent8_tests import split_fast

@lru_cache(None)
def allowed(f,i):
 N,Phi,FT,FA=project(f,i)
 H4=frontdata(f,i)[8]
 B=bg(C(term0(H4,s).resultant(L4(g*s),1)))
 G=unef(egcd(ef(N),ef(B)));D=unef(eguard(ef(N),[ef(B)]));PH=bsg(Phi)
 exact=exact_allowed(squarefree(G),PH,H4) if len(G)>1 else []
 regular=[(P,PH[:j+1],j) for P,j in split_fast(D,PH)] if len(D)>1 else []
 assert (len(G)-1,len(D)-1)==(12,283)
 assert [(len(P)-1,len(Q)-1,j) for P,Q,j in exact+regular]==[(12,2,3),(127,3,3),(12,2,2)]
 print('no-front star exact fourth branches:',f,i,len(G)-1,len(D)-1,[(len(P)-1,len(Q)-1,j) for P,Q,j in exact+regular],flush=True)
 return exact+regular

def phase(f,i,p,t):
 fd=frontdata(f,i);A,B,q0p,q1p,_=gauge(f,i)
 n=0
 for G,Phi,deg in allowed(f,i):
  assert len(Phi)>1
  for F,g in gammas(G,p,t):
   gg=lambda p:ev(list(map(F,p)),g)
   Q=trim([gg(v) for v in Phi]);assert len(Q)==len(Phi)
   W=Tower(mon(Q));s=W.gen()
   n+=1
   V=-gg(A)/gg(B);q0,q1=gg(q0p),gg(q1p);xi=W(-q0/q1)
   ga=W(g);a,b,ha=map(W,fd[5:8]);H4=list(map(W,fd[8]))
   x=1-ga;m=x-ga
   R=mul(mul([-x,W(1)],[-ga*s,W(1)]),[m*m-ga*ga*W(V),-2*m,W(1)])
   N3=cmask(W,ga,mmask(W,R,xi,6),3)
   L=list(map(W,Lco));La=ev(L,ga*a)
   Qp=[La*W(q0),La*W(q1)*ga]
   Pp=[ha*(W(q0)+W(q1)*ga*a)*v*ga**j for j,v in enumerate(L)]
   h,T0,A0,T1,A1=fterms(W,fd,a,s,H4)
   T=add(sc(mul(T0,Qp),h),mul(T1,Pp))
   B0=add(sc(mul(A0,Qp),h),mul(A1,Pp))
   D0=list(map(W,nodal([a,s])))
   T,e=qr(T,D0);assert not e
   B0,e=qr(B0,D0);assert not e
   assert test_unit(W,polyres(W,T,B0,3,3),polyres(W,N3,T,3,3),polyres(W,N3,B0,3,3))
 assert n
 print('verified no-front star literal fifth:',f,i,p,n,flush=True)
 return True
