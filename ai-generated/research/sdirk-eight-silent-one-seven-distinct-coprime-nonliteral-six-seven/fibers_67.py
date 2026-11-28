"""All retained ordinary-fifth nodal fibers for actual separate transport at 6/7."""
from star_67 import *
from arithmetic_crt import arith_inputs
from arithmetic_fibers import fast_s_fields
from fifth_fibers import cv_poly,deg_ok,anchor_vars,nodal_y5,unit_b,test_unit
from leading_branch import polyres
from collections import Counter

def input67(f,i,r):
 return star67(f,i) if r else arith_inputs(f,i)

def fibers67(f,i,r,p=1103,t=161):
 J,P,T,A,D,Q0,E,N=input67(f,i,r)
 G=degree_safe_reduction(J,P,p,t)
 assert G.degree()==((660 if f else 693) if r else (2300 if f else 2416))
 fd=frontdata(f,i);out=[];co=Counter()
 for M,U,g,s in fast_s_fields(J,P,G,p,t,out):
  co['s']+=1
  R0=cv_poly(E,U,[None,s,None,g],2);R1=cv_poly(N,U,[None,s,None,g],2)
  if not (deg_ok(R0,E,2) or deg_ok(R1,N,2)):
   out.append(('gap nominal leader',M.degree(),len(U.F)-1,str(M)))
   continue
  B0=gcdp(R0,R1)
  if len(B0)<=1:continue
  co['gap']+=1
  V=Nested(mon(B0));g,s=V(g),V(s)
  if r:
   W=Nested([-V.gen(),V(0),V(1)]);u=1+W.gen()
   g,s=W(g),W(s)
  else:
   W=V;u=W.gen()
  a,q0,q1=anchor_vars(Q0,W,g,s,fd[5])
  x=1-g;c=x-g*u;d=x-g*(2-u if r else 2*u)
  Y=nodal_y5(W,g,[g*a,x,c,d],q0,q1)
  Y,r0=qr(Y,[-s,W(1)])
  assert not r0
  # The only divided (Y-s) is distinct for ordinarily active fifth.
  P1,P2,P3=[cv_poly(F,W,[None,s,None,g],0) for F in (T,A,D)]
  xs=[polyres(W,P1,P2,3,3),polyres(W,P1,Y,3,2),polyres(W,P2,Y,3,2),polyres(W,P3,Y,3,2)]
  if test_unit(W,*xs):
   co['fifth passes']+=1;continue
  L0=list(map(W,Lco));k=1+2*u-u*u;b=W(fd[6])
  q=lambda t:q0+q1*t
  hs=ev(list(map(W,fd[8])),s)
  checks=[('u',u),('k',k),('s=b allowed',s-b),('s−a',s-a),('H4',hs),('La',ev(L0,g*a)),
          ('Ls',ev(L0,g*s)),('qx',q(x)),('qc',q(c)),('qd',q(d)),('Lc',ev(L0,c)),('Ld',ev(L0,d)),
          ('c=d',c-d),('c=ga',c-g*a),('d=ga',d-g*a),('c=gs',c-g*s),('d=gs',d-g*s)]
  out.append(('ordinary fifth residual',M.degree(),len(U.F)-1,len(B0)-1,
              [name for name,z in checks if not unit_b(W,z)],str(M)))
 print('j6/j7 same actual fifth nodal census',f,i,r,p,G.degree(),dict(co),out,flush=True)
 return out
