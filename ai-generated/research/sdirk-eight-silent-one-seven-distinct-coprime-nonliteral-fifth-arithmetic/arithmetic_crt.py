"""Height-bounded bivariate arithmetic rear resultant and outer diagonal."""
from arithmetic_nodal import *
from nonliteral_fourth_crt import int_rows,resultant_mod,prime_seq
from flint import nmod_mpoly_ctx
from math import factorial,lcm
from time import perf_counter

def int_rows_u(F):
 T={};d=1
 for (i,j,k,l,m),a in F.to_dict().items():
  assert not i
  if m:a/=2
  d=lcm(d,int(a.q))
  r=T.setdefault((k,j,l),[Q(0),Q(0)])
  r[m]+=a
 z={e:(int(a*d),int(b*d)) for e,(a,b) in T.items()}
 assert all(a*d==z[u][0] and b*d==z[u][1] for u,(a,b) in T.items())
 return z,sum(abs(a)+2*abs(b) for a,b in z.values()),d

def prep(F,G):
 A,a,da=int_rows_u(F);B,b,db=int_rows_u(G)
 m,n=F.degrees()[2],G.degrees()[2]
 H=factorial(m+n)*a**n*b**m
 return A,B,m,n,H,da,db

def mod_proj(W,p,w):
 A,B,m,n,H,da,db=W
 C=nmod_mpoly_ctx.get(['u','s','g'],modulus=p)
 S=C.from_dict({z:(a+w*b)%p for z,(a,b) in A.items()})
 T=C.from_dict({z:(a+w*b)%p for z,(a,b) in B.items()})
 if S.degrees()[0]!=m or T.degrees()[0]!=n:return None
 R=S.resultant(T,0)
 assert not R or not R.degrees()[0]
 D={(j,k):int(b) for (i,j,k),b in R.to_dict().items()}
 return D

def red_coords(F,p,t):
 Md={}
 for (i,j,k,l,m),c in F.to_dict().items():
  assert not i and not k
  Md[j,l]=(Md.get((j,l),0)+pow(t,m,p)*int(c.p)*pow(int(c.q),-1,p))%p
 return {e:a for e,a in Md.items() if a}

def bivar(W,label):
 H=W[4]; aa={};bb={};mm=1;j=0;st=perf_counter()
 for p,w in prime_seq():
  M,N=mod_proj(W,p,w),mod_proj(W,p,-w)
  if M is None or N is None:continue
  q=pow(mm,-1,p);sw=pow(2*w,-1,p);s2=pow(2,-1,p)
  for e in M.keys() | N.keys() | aa.keys() | bb.keys():
   a,b=M.get(e,0),N.get(e,0);x,y=aa.get(e,0),bb.get(e,0)
   aa[e]=x+mm*(((a+b)*s2-x)*q%p)
   bb[e]=y+mm*(((a-b)*sw-y)*q%p)
  mm*=p;j+=1
  if j==1 or j%8==0:print('j5 bivariate CRT',label,j,mm.bit_length(),H.bit_length(),len(aa),round(perf_counter()-st,2),flush=True)
  if mm>2*H:
   ctr=lambda a:a-mm if 2*a>mm else a
   ya={(0,r,0,s,0):ctr(a) for (r,s),a in aa.items() if ctr(a)}
   yb={(0,r,0,s,1):2*ctr(b) for (r,s),b in bb.items() if ctr(b)}
   assert max(map(abs,ya.values()),default=0)<=H and max(map(abs,yb.values()),default=0)<=2*H
   F=CX.from_dict({**ya,**yb})
   assert F and red_coords(F,1103,161)==mod_proj(W,1103,322)
   print('j5 exact projected u norm',label,F.degrees(),len(ya)+len(yb),flush=True)
   return F

@lru_cache(None)
def arith_inputs(f,i):
 J,T,A,D,Q0,F,N=nodal_projection(f,i)
 R=bivar(prep(F,N),(f,i))
 assert R.degrees()==(0,81,0,189,1)
 a=C(frontdata(f,i)[5]);H=term(frontdata(f,i)[8],s)
 q0,q1=coeff_var(Q0,0);q0=fold(g*q0)
 X=1-g
 simple=[g,s-a,H,L(g*a),L(X),X-g*a,L(g*s),X-g*s]
 qx=fold(q0+X*q1);qx,kx=guard_strip(qx,simple)
 cs,ks=guard_strip(q1,simple)
 simple.extend((qx,cs))
 qres=fold(sum(Lco[j]*(-q0)**j*q1**(4-j) for j in range(5)))
 qres,nq=guard_strip(qres,simple)
 R,nn=guard_strip(R,[*simple,qres])
 print('true coprime affine Gauss divisor',f,i,qres.degrees(),nq,nn[-1],flush=True)
 assert nn==[13,0,0,2,0,0,7,0,0,0,2]
 assert R.degrees()==(0,37,0,116,1)
 print('j5 exact new diagonal inputs',f,i,J.degrees(),R.degrees(),nn,flush=True)
 return J,R,T,A,D,Q0,F,N

def pack_outer(F,G):
 A,a,da=int_rows(F);B,b,db=int_rows(G)
 m,n=F.degrees()[1],G.degrees()[1]
 N=m*G.degrees()[3]+n*F.degrees()[3]
 H=factorial(m+n)*a**n*b**m
 return A,B,m,n,N,H,da,db


def degree_safe_reduction(J,P,p,t):
 from sympy import isprime
 assert isprime(p) and 2*t*t%p==1
 W=pack_outer(J,P)
 assert W[-1]%p and W[-2]%p
 F=resultant_mod(W,p,2*t)
 assert F and F.degree()==W[4]
 # Degree reaches the exact upper bound as well as the finite one.
 return F*pow(int(F.leading_coefficient()),-1,p)

from shared_silent8_projection import red_e
