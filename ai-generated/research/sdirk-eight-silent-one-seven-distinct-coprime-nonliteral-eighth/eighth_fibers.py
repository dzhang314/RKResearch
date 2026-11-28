"""Complete local residues or a guarded frontier for sole silent eighth."""
from eighth_projection import *
from fifth_fibers import cv_poly,deg_ok,anchor_vars,nodal_y5,unit_b,test_unit,ff_factors
from shared_arith_checks import inverse_one
from leading_branch import polyres
from collections import Counter
from flint import nmod_poly
from sixth_literal import sixth_residual

def monic_choice(W,C,n):
 N=[(A+[W(0)]*(n+1-len(A))) for A in C]
 assert all(len(A)==n+1 for A in N)
 for A in N:
  if unit_b(W,A[-1]):return sc(A,inverse_one(W,A[-1]))
 for k in range(1,24):
  P=[sum((k**j * A[r] for j,A in enumerate(N)),W(0)) for r in range(n+1)]
  if unit_b(W,P[-1]):return sc(P,inverse_one(W,P[-1]))
 return None

def u_coefficients(R,p,t):
 A=E_su(R);m=R.degrees()[2]
 Z=nmod_poly([],p)
 return [[red_e(a[k],p,t) if k<len(a) else Z for a in A]
         for k in range(m+1)]

def eval_gap(X,U,s):
 F=U.B
 return trim([ev([U(F(a)) for a in A],s) for A in X])

def s_fields(J,P,H,p,t,fail):
 V0,V1=([red_e(row[0] if row else E(0),p,t) for row in E_su(R)] for R in (J,P))
 assert H.modulus()==p and int(H.leading_coefficient())==1
 fac=H.factor()[1]
 print('j8 diagonal reduced factor count',len(fac),flush=True)
 for M,_ in fac:
  F=Bfield(M,p,t);g=F(nmod_poly([0,1],p))
  J0=trim(list(map(F,V0)));P0=trim(list(map(F,V1)))
  if not (deg_ok(J0,J,1) or deg_ok(P0,P,1)):
   fail.append(('s monic',M.degree(),str(M)));continue
  C0=gcdp(J0,P0)
  if len(C0)<=1:continue
  fs=[mon(C0)] if len(C0)==2 else ff_factors(F,C0,p)
  for S in fs:
   U=Tower(mon(S))
   yield M,U,U(g),U.gen()

def eighth_fibers(f,i,p=1103,t=161):
 J,P,T,A,D,Q0,E,N,P0=inputs8(f,i)
 G=degree_safe_reduction(J,P,p,t)
 assert G.degree()==(3780 if f else 3951)
 fd=frontdata(f,i);out=[];co=Counter()
 es,ps=u_coefficients(E,p,t),u_coefficients(P0,p,t)
 for M,U,g,s in s_fields(J,P,G,p,t,out):
  co['s']+=1
  if co['s']%10==0:print('j8 s fibers completed',f,i,co['s'],M.degree(),flush=True)
  E0=eval_gap(es,U,s);E1=eval_gap(ps,U,s)
  if not (deg_ok(E0,E,2) or deg_ok(E1,P0,2)):
   out.append(('gap nominal lead',M.degree(),len(U.F)-1,str(M)))
   continue
  e=gcdp(E0,E1)
  if len(e)<=1:continue
  co['gap']+=1
  W=Nested(mon(e));u=W.gen();g,s=W(g),W(s)
  q=coeffs=[cv_poly(F,W,[None,s,u,g],0) for F in (T,A,D,N)]
  d=[F.degrees()[0] for F in (T,A,D,N)]
  xx=[polyres(W,q[j],q[k],d[j],d[k]) for j in range(4) for k in range(j+1,4)]
  if test_unit(W,*xx):
   co['fifth pairwise passes']+=1;continue
  a,q0,q1=anchor_vars(Q0,W,g,s,fd[5])
  b=W(fd[6]);x=1-g;c=x-g*u;k=1+2*u-u*u;z=x+g*k*(u-2)/2
  q=lambda x:q0+q1*x
  LL=list(map(W,Lco))
  fl=[('u',u),('u=2',u-2),('k',k),('q1',q1),('c=gs',c-g*s),('c=ga',c-g*a),('Lc',ev(LL,c)),
      ('qc',q(c)),('qx',q(x)),('qz',q(z)),('c=z',c-z),('gs=z',g*s-z),('ga=z',g*a-z)]
  fv=[name for name,xx in fl if not unit_b(W,xx)]
  Y=monic_choice(W,coeffs,max(d))
  if Y is None:
   out.append(('y genuine leading',M.degree(),len(U.F)-1,len(e)-1,fv,str(M)))
   continue
  V=Nested(Y);y=V.gen()
  v=[ev(list(map(V,F)),y) for F in coeffs if F]
  if test_unit(V,*v):
   co['fifth simultaneous passes']+=1;continue
  g,s,a,b,c,z,x,q0,q1=map(V,(g,s,a,b,c,z,x,q0,q1))
  rs=sixth_residual(V,fd,g,s,y,q0,q1,[g*a,g*s,x,c,g*y])
  if test_unit(V,*v,*rs):
   co['literal sixth passes']+=1;continue
  yy=[('y=a',y-a),('y=s',y-s),('y=b allowed',y-b),('y=z',g*y-z),('y=x',g*y-x),('y=c',g*y-c),('Ly',ev(list(map(V,Lco)),g*y))]
  out.append(('actual fifth common residual',M.degree(),len(U.F)-1,len(e)-1,len(Y)-1,fv,
              [n for n,x in yy if not unit_b(V,x)],str(M)))
 print('j8 finite residue census',f,i,p,G.degree(),dict(co),out,flush=True)
 return out
