"""Arithmetic rear j5: monic gap and homogeneous actual fifth residual checks."""
from arithmetic_crt import *
from fifth_fibers import cv_poly,ff_factors,deg_ok,anchor_vars,unit_b,test_unit
from flint import nmod_poly
from collections import Counter

def hom(F,P,n,d,N):
 assert len(P)<=N+1
 return sum((p*n**i*d**(N-i) for i,p in enumerate(P)),F(0))

def fast_s_fields(J,P,H,p,t,fail):
 V0,V1=([red_e(row[0] if row else E(0),p,t) for row in E_su(R)] for R in (J,P))
 assert H.modulus()==p and int(H.leading_coefficient())==1
 for M,_ in H.factor()[1]:
  F=Bfield(M,p,t);g=F(nmod_poly([0,1],p))
  J0=trim(list(map(F,V0)));P0=trim(list(map(F,V1)))
  if not (deg_ok(J0,J,1) or deg_ok(P0,P,1)):
   fail.append(('s monic',M.degree(),str(M)));continue
  C0=gcdp(J0,P0)
  if len(C0)<=1:continue
  for S in ff_factors(F,C0,p):
   U=Tower(mon(S));s=U.gen()
   yield M,U,U(g),s

def arith_fibers(f,i,H,p,t):
 J,P,T,A,D,Q0,E,N=arith_inputs(f,i)
 fd=frontdata(f,i);out=[];co=Counter()
 for M,U,g,s in fast_s_fields(J,P,H,p,t,out):
  co['s']+=1
  e=cv_poly(E,U,[None,s,None,g],2);n=cv_poly(N,U,[None,s,None,g],2)
  if not (deg_ok(e,E,2) or deg_ok(n,N,2)):
   out.append(('u monic',M.degree(),len(U.F)-1,str(M)));continue
  B0=gcdp(e,n)
  if len(B0)<=1:continue
  co['u algebra']+=1
  W=Nested(mon(B0));u=W.gen();g,s=W(g),W(s)
  a,q0,q1=anchor_vars(Q0,W,g,s,fd[5]);b=W(fd[6])
  x=1-g;c=x-g*u;d=x-2*g*u;k=1+2*u-u*u
  Qr=lambda v:q0+q1*v
  LL=list(map(W,Lco));l8,l9,l10=map(lambda v:ev(LL,v),(d,c,x))
  Aa=Qr(x)*l9-k*Qr(c)*l10
  Bb=g*u*k*Qr(c)*l10
  den=g*Aa;num=x*Aa+Bb
  gates=[hom(W,cv_poly(F,W,[None,s,None,g],0),num,den,F.degrees()[0]) for F in (T,A,D)]
  if test_unit(W,*gates):
   co['fifth residual passes']+=1;continue
  hs=ev(list(map(W,fd[8])),s)
  fflags=[('gamma',g),('u',u),('k',k),('q1',q1),('s-a',s-a),('s=b allowed',s-b),
          ('H4',hs),('Ls',ev(LL,g*s)),('qs',Qr(g*s)),('s=x',g*s-x),('La',ev(LL,g*a)),('qx',Qr(x)),('qc',Qr(c)),('qd',Qr(d)),('Lc',l9),('Ld',l8),('Lx',l10),
          ('den',den),('num',num),('x-z',x*den-g*num),('c-z',c*den-g*num),('d-z',d*den-g*num),
          ('qz',q0*den+q1*g*num),('y-a',num-den*a),('y-b',num-den*b),('y=s',num-den*s)]
  out.append(('fifth',M.degree(),len(U.F)-1,len(B0)-1,[q for q,a0 in fflags if not unit_b(W,a0)],str(M)))
 print('j5 arithmetic finite census',f,i,p,H.degree(),dict(co),out,flush=True)
 return out
