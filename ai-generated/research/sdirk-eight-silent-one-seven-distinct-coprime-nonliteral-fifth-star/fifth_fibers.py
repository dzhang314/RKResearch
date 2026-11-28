"""Monic residues for the same physical fifth, with zero virtual h allowed."""
from star_fifth import *
from fifth_crt import rec,data,resultant_mod
from nonliteral_fourth_closed_fibers import cv_poly,at
from nofront_residue import ff_factors
from leading_branch import nodal_y5,unit_b,test_unit
from shared_arith_checks import inverse_one
from shared_silent8_projection import red_e
from flint import nmod_poly
from collections import Counter

def scalar(W,F,y,s,u,g):
 R=cv_poly(W,F,[None,s,u,g],0)
 return ev(R,y) if R else F(0)

def deg_ok(a,W,d):return len(a)==W.degrees()[d]+1
def gpolynomials(H,p,t):
 A=red_e(H,p,t)
 assert A.degree()==H.degree() and int(A.leading_coefficient())==1
 for M,_ in A.factor()[1]:
  F=Bfield(M,p,t);gg=F(nmod_poly([0,1],p))
  yield M,F,gg

def Sfields(J,P,H,p,t,fail):
 for M,F,g in gpolynomials(H,p,t):
  J0=cv_poly(J,F,[None,None,None,g],1);P0=cv_poly(P,F,[None,None,None,g],1)
  if not (deg_ok(J0,J,1) or deg_ok(P0,P,1)):
   fail.append(('s monic',M.degree(),str(M)));continue
  C0=gcdp(J0,P0)
  if len(C0)<=1:continue
  for S in ff_factors(F,C0,p):
   U=Tower(mon(S));s=U.gen();gg=U(g)
   yield M,U,gg,s

def fifth_carrier(U,g,s,polys,out,M):
 coeffs=[cv_poly(F,U,[None,s,None,g],0) for F in polys]
 if not any(deg_ok(P,F,0) for P,F in zip(coeffs,polys)):
  out.append(('y monic',M.degree(),len(U.F)-1,str(M)));return None
 G=coeffs[0]
 for P in coeffs[1:]:G=gcdp(G,P)
 if len(G)<=1:return None
 W=Nested(mon(G))
 return W,W(g),W(s),W.gen()

def anchor_vars(Q0,W,g,s,a0):
 a=W(a0)
 q0,q1=coeff_var(Q0,0)
 at_s=lambda H:at(H,W,g,s)
 return a,g*at_s(q0),at_s(q1)

def guards5(W,g,s,y,a,b,q0,q1,H4):
 x=1-g;z=g*y;Lt=list(map(W,Lco));hs=ev(list(map(W,H4)),s)
 nn=[('gamma',g),('x-z',x-z),('qx',q0+q1*x),('qz',q0+q1*z),('q1',q1),('H4',hs),('Lx',ev(Lt,x)),
     ('La',ev(Lt,g*a)),('y=a',y-a),('y=b',y-b),('y=s',y-s)]
 out=[n for n,q in nn if not unit_b(W,q)]
 if not unit_b(W,ev(Lt,z)):out.append('L4(z) zero allowed')
 return out

def star_fibers(f,i,H,p,t):
 J,P,K,T,A,D,Q0,V=star(f,i)
 fd=frontdata(f,i);out=[];co=Counter()
 for M,U,g,s in Sfields(J,P,H,p,t,out):
  co['s']+=1
  XY=fifth_carrier(U,g,s,[D,K,T,A],out,M)
  if XY is None:continue
  W,g,s,y=XY
  co['fifth candidate']+=1
  a,qa,qb=anchor_vars(Q0,W,g,s,fd[5]);b=W(fd[6])
  f0,f1,f2,f3=[scalar(R,W,y,s,None,g) for R in V]
  br=guards5(W,g,s,y,a,b,qa,qb,fd[8])
  for k in [0,1,*range(2,20),None]:
   n,d=(f1,f3) if k is None else (f0+k*f1,f2+k*f3)
   if unit_b(W,d):
    v2=-n*inverse_one(W,d)
    break
  else:
   out.append(('centered slope monic',M.degree(),len(W.F)-1,br,str(M)))
   continue
  # Use the actual center; both v signs are retained even when p-ramified.
  C=Nested([-v2,W(0),W(1)]);v=C.gen();u=1+v
  g,s,y,a,qa,qb=map(C,(g,s,y,a,qa,qb))
  x=1-g;c=x-g*u;d=x-g*(2-u)
  N=ev(nodal_y5(C,g,[g*a,x,c,d],qa,qb),s)
  F1,F2=[C(x0) for x0 in (f0+f2*v2,f1+f3*v2)]
  if not test_unit(C,F1,F2,N):
   Ls=list(map(C,Lco))
   kt=1+2*u-u*u;z=g*y
   z0=[name for name,q in [('k',kt),('u',u),('c=d',c-d),('c=z',c-z),('d=z',d-z),('qc',qa+qb*c),('qd',qa+qb*d),('Lc',ev(Ls,c)),('Ld',ev(Ls,d))]
           if not unit_b(C,q)]
   out.append(('signed nodal',M.degree(),len(W.F)-1,br,z0,str(M)))
  else:co['monic residual passes']+=1
 print('j5 star finite residue census',f,i,p,H.degree(),dict(co),out,flush=True)
 return out

def run_star(f,i):
 H=rec(f,i,'star');p,t=1103,161
 M=resultant_mod(data(f,i),p,2*t)
 assert 2*t*t%p==1
 assert M and M.degree()==H.degree()==(768 if f else 807) and red_e(H,p,t)==M
 return star_fibers(f,i,H.monic(),p,t)
