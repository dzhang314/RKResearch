"""Nonliteral distinct Gauss and reverse roots, star or arithmetic Gauss eighth."""
from front_gauss_nonliteral import *
from gauss_tail_nonliteral import p0,aX,gX,rX,B0,by_g,remR

@lru_cache(None)
def Gstar():
 F=remR(-2*p0(aX)-gX*gX*(420*aX-280+140*rX)+280*gX**3)
 J=mon(by_g(F));assert len(J)==4
 return J

def star_check(f,i,p,t):
 fd=frontdata(f,i)
 assert len(gcdp(fd[8],exact_uc_y(fd[19])))==1
 n=0
 for F,g,r,lift in cut_gamma(Gstar(),p,t):
  n+=1
  a,b,ha=map(F,fd[5:8])
  H4=list(map(F,fd[8]))
  P0=[g**j*q for j,q in enumerate(Pcoeff(F,r))]
  Q,P=ev(P0,a),sc(P0,ha)
  P4,err=qr(add(sc(H4,Q),sc(P,-1)),[-a,F(1)])
  assert not err and len(P4)==3
  S=Tower(mon(P4));s=S.gen()
  assert test5(S,S(g),S(r),S(a),s,list(map(S,H4)),fd,S(Q),list(map(S,P)),6,0)
 assert n
 print('verified cubic star diagonal:',f,i,p,n,flush=True)
 return True

def hole_moment(F,g,r,pegs):
 L=Pcoeff(F,r);nu=intp(F,L)/ev(L,r)
 T=nodal(pegs);Tr=ev(T,r)
 m0,m1,m2,m3=[intp(F,T,i)-nu*Tr*r**i for i in range(4)]
 return [m1*m3-m2*m2,(m1*m2-m0*m3)*g,(m0*m2-m1*m1)*g*g]
