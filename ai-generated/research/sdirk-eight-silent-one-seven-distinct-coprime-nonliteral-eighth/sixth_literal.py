"""An actual ordinary sixth read with no literal clock differences inverted."""
from star_fifth import *
from extra_active import bezout
from off8_fibers import det,cramer
from leading_branch import polyres
from front_gauss_nonliteral import fterms
from itertools import combinations

def six_polynomial(W,fd,g,s,y,q0,q1):
 A,B,ha,hb=map(W,(fd[0],fd[1],fd[3],fd[4]))
 a,h_a=map(W,(fd[5],fd[7]))
 H=ev(list(map(W,fd[8])),s)
 tau,ah=map(W,fd[11:13])
 XT=ev(list(map(W,exact_uc_y(fd[14]))),s)
 XA=ev(list(map(W,exact_uc_y(fd[15]))),s)
 Qc=[q0,g*q1]
 Pc=[g*h_a*H*(s-a)*W(r)*g**j for j,r in enumerate(Lco)]
 Qy=ev(Qc,y);Py=ev(Pc,y)
 readT=[H*(tau-2)-XT*a,XT]
 readA=[H*(ah-1)-XA*a,XA]
 HD=sc(Qc,H)
 mom=[add(mul(HD,m),sc(Pc,-H*d)) for m,d in zip(
         [[W(-1),W(1)],[W(0),W(-1),W(1)/2],[W(0),W(0),W(-1),W(1)/3]],
         (W(2),W(2),W(4)/3))]
 mom.append(add(mul(HD,[W(0)]*3+[W(-1),W(1)/4]),mul(Pc,readT)))
 mom.append(mul(Pc,readA))
 def at_eta(hy):
  rows=[[W(1),z,z*z,z**3,q] for z,q in ((A,ha),(B,hb),(s,H),(y,hy))]
  cof=[(-1)**j*det([[r[k] for k in range(5) if k!=j] for r in rows]) for j in range(5)]
  return sum_poly([sc(a,b) for a,b in zip(mom,cof)])
 C0=at_eta(W(0));C1=add(at_eta(W(1)),sc(C0,-1))
 h,T0,A0,T1,A1=fterms(W,fd,a,s,list(map(W,fd[8])))
 assert h==H
 return [add(sc(C0,Qy),sc(C1,Py)),
         add(sc(C0,ev(T1,y)),sc(C1,-H*ev(T0,y))),
         add(sc(C0,ev(A1,y)),sc(C1,-H*ev(A0,y)))]


def missing_quad_options(W,g,pegs,q0,q1):
 L=list(map(W,Lco));M=mon(L)
 G=list(map(W,nodal(pegs)))
 H0,H1,H2=(qr([W(0)]*j+G,M)[1] for j in range(3))
 H0,H1,H2=(A+[W(0)]*(4-len(A)) for A in (H0,H1,H2))
 v=bezout();cs=[q0*q0,2*q0*q1,q1*q1]
 Z=[sum((cs[j]*W(v[j][k]) for j in range(3) if k<len(v[j])),W(0)) for k in range(4)]
 vals=[]
 for I in combinations(range(4),3):
  X=[[H0[i],H1[i],Z[i]] for i in I]
  C0,C1,C2=cramer(X,[-H2[i] for i in I])
  vals.append([C0,C1*g,det(X)*g*g])
 return vals

def sixth_residual(W,fd,g,s,y,q0,q1,pegs):
 n=missing_quad_options(W,g,pegs,q0,q1)
 R=six_polynomial(W,fd,g,s,y,q0,q1)
 assert all(len(P)<=6 for P in R)
 return [polyres(W,P,Q0,5,2) for P in R for Q0 in n]
