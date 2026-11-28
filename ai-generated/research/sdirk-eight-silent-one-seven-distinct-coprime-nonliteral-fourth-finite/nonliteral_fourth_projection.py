"""A single honest transported fourth: separate front and tail constraints."""
from nofront_arith_cross import *
from functools import lru_cache
from math import prod

def strip_poly(W,D):
 assert W and D
 while True:
  q,r=div(W,D)
  if r:return W
  W=q

@lru_cache(None)
def profiles(f,i):
 A,B,m,ha,hb,a,b,hh,H4,L0,e,tau,ah,HS,XT,XA,DT,DA,*_=frontdata(f,i)
 A,B,a,b=map(C,(A,B,a,b));h=C(hh);H=term(H4,s)
 # The other literal b is not an anchor. Both read anchors really have
 # the same active rational profile: literal a is active and fourth s alone transports.
 Q0=fold(H*L(g*a)*(s-y)+h*L(g*s)*(y-a))
 P0=fold(h*H*(s-a)*L(g*y))
 m0=y-1;m1=y*y/2-y;m2=y**3/3-y*y
 M=m2-(A+B)*m1+A*B*m0
 T0=fold(y**3-y**4/4+(A+B)*m2-A*B*m1+s*M)
 A0=fold(C(L0[0])*m0+C(L0[1])*m1+term(e,s)*M)
 T1=fold(H*(term(DT,s)-C(tau))-term(exact_uc_y(XT),s)*(y-a))
 A1=fold(H*(term(DA,s)-C(ah))-term(exact_uc_y(XA),s)*(y-a))
 D=exdiv(exdiv(fold(T0*A1-A0*T1),y-a),y-s)
 T=exdiv(exdiv(fold(H*T0*Q0+T1*P0),y-a),y-s)
 V=exdiv(exdiv(fold(H*A0*Q0+A1*P0),y-a),y-s)
 T,V=(strip_poly(strip_poly(F,H),s-a) for F in (T,V))
 J=fold(T.resultant(D,0));assert J
 good0=[g,s-a,s-b,H,L(g*a),L(g*s),1-g-g*s]
 for z in good0[:4]:J=strip_poly(J,z)
 print('active-literal transported-fourth front',f,i,T.degrees(),V.degrees(),D.degrees(),J.degrees(),flush=True)
 return J,T,V,D,Q0,P0,good0

def subst_var(P,j,z):
 return fold(sum(a*z**d[j]*prod(W**k for i,(k,W) in enumerate(zip(d,(y,s,u,g,t))) if i!=j)
                  for d,a in P.to_dict().items()))

def coeff_var(W,j):
 d=W.degrees()[j]
 O=[CX.constant(0)]*(d+1)
 for q,b in W.to_dict().items():
  v=list(q);v[j]=0
  O[q[j]]+=CX.from_dict({tuple(v):b})
 return O

@lru_cache(None)
def tail_pair(f,i,star):
 Fr,T,V,D,Q0,P0,gds=profiles(f,i)
 x=1-g;c=x-g*u;z=g*s;d=x-g*(2-u if star else 2*u)
 q=lambda X:fold(g*coeff_var(Q0,0)[0]+X*coeff_var(Q0,0)[1])
 k=1+2*u-u*u
 R=fold(q(x)*(x-z)*L(c)-k*q(c)*(c-z)*L(x))
 R=strip_poly(R,u)
 for a in gds[:4]:R=strip_poly(R,a)
 if star:
  C0=coeff_var(subst_var(R,2,u+1),2);assert len(C0)==4
  K=fold(C0[0]*C0[3]-C0[1]*C0[2])
  S=coeff_var(subst_var(R,2,2-u),2)
  print('literal shared fourth star gap is affine even/odd',f,i,C0[2].degrees(),C0[3].degrees(),flush=True)
  P=[C0[0],C0[2]];Q1=[C0[1],C0[3]]
 else:
  H=-2+u+4*u*u-u**3;A=4*u**3-12*u*u+3*u+2
  S=fold(H*q(x)*(x-z)*L(d)+k*A*q(d)*(d-z)*L(x))
  S=strip_poly(S,u)
  for a in gds[:4]:S=strip_poly(S,a)
  K=fold(R.resultant(S,2));assert K
  P,Q1=R,S
 for a in gds[:4]:K=strip_poly(K,a)
 print('active-literal actual transported-fourth tail',f,i,star,R.degrees(),K.degrees(),flush=True)
 return K,P,Q1

def s_phase(W,gg):
 A=E_su(fold(subst_var(W,3,CX.constant(gg))));assert all(len(x)<=1 for x in A)
 return [F2(x[0]) if x else F2(0) for x in A]

def verify(f,i,star):
 J=profiles(f,i)[0]
 K,*_=tail_pair(f,i,star)
 for q in map(Q,(1,2,3,4,5,7)):
  F,G=s_phase(J,q),s_phase(K,q)
  if (len(F)-1,len(G)-1)!=(J.degrees()[1],K.degrees()[1]):continue
  C=gcdp(F,G)
  print('exact common fourth factors at gamma probe',f,i,star,q,len(C)-1,flush=True)
  if len(C)==1:return True
 return False

if __name__=='__main__':
 from itertools import product
 from math import prod
 for f,i,r in product((True,False),(0,1),(True,False)):
  print('nonliteral physical-fourth finite diagonal?',f,i,r,verify(f,i,r),flush=True)
