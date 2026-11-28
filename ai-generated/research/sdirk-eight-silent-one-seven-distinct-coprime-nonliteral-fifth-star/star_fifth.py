"""Genuinely nonliteral actual fifth: exact two-anchor front and affine star rear."""
from itertools import product
from nonliteral_fourth_tight import *
from nonliteral_fourth_content import gamma_of,cg,as_es

def guard_strip(W,guards):
 print0=[]
 for a in guards:
  W,n=strip_exact(W,fold(a))
  print0.append(n)
 return W,print0

@lru_cache(None)
def front(f,i):
 fd=frontdata(f,i)
 _,T,A,D,Q0,P0,gg=profiles(f,i)
 # Do not inherit the j=4 resultant with a possible s-b factor removed:
 # active fourth can share a clock with the weight-zero literal b.
 a,b=map(C,fd[5:7])
 gs=[g,s-a,gg[3]]
 T,nt=strip_exact(T,gg[3]);A,na=strip_exact(A,gg[3])
 assert (nt,na)==((0,0) if f else (1,1))
 J,tj=guard_strip(fold(T.resultant(D,0)),gs)
 assert J
 assert len(gcdp(fd[8],exact_uc_y(fd[19])))==1
 return J,T,A,D,Q0,P0,gs,a,b

@lru_cache(None)
def star(f,i):
 J,T,A,D,Q0,P0,gs,a,b=front(f,i)
 q0,q1=coeff_var(Q0,0)
 X=1-g;C1=X-g*u;Z=g*y;Xz=X-Z
 qx=fold(g*q0+X*q1)
 k=1+2*u-u*u;Lx=L(X);U=fold(qx*Xz);B0=qx+q1*Xz-g*q1;B1=-g*q1
 PC=coeff_var(subst_var(exdiv(fold(L(C1)-k*Lx),u),2,u+1),2)
 K=fold(U*(PC[0]*PC[3]-PC[1]*PC[2])+g*Lx*(B0*(2*PC[3]+PC[1])-B1*(PC[0]+2*PC[2])))
 R=exdiv(fold(qx*Xz*L(C1)-k*(g*q0+C1*q1)*(C1-Z)*Lx),u)
 V=coeff_var(subst_var(R,2,u+1),2)
 assert len(V)==4
 assert fold(V[0]*V[3]-V[1]*V[2]-U*K)==CX.constant(0)
 K,tk=guard_strip(K,gs)
 assert K.degrees()[0]==1
 P,tp=guard_strip(fold(D.resultant(K,0)),gs)
 assert P
 print('j5 star finite projected degrees',f,i,J.degrees(),P.degrees(),[tk,tp],flush=True)
 return J,P,K,T,A,D,Q0,V

def check_star(f,i):
 J,P,K,T,A,D,Q0,V=star(f,i)
 Jym=[w[0] for w in E_su(J) if w];Pym=[w[0] for w in E_su(P) if w]
 q=cg(Jym);r=cg(Pym)
 print('j5 star exact content',f,i,q.degree(),r.degree(),flush=True)
 assert q.degree()==0
 assert cg(map(as_es,coeff_var(D,0))).degree()==0
 for z in map(Q,(1,2,3,4,5,7)):
  A=s_phase(J,z);B=s_phase(P,z)
  if len(A)-1!=J.degrees()[1] or len(B)-1!=P.degrees()[1]:continue
  X=gcdp(A,B)
  print('j5 star exact coprimality specialization',f,i,z,len(X)-1,flush=True)
  if len(X)==1:return True
 return False
