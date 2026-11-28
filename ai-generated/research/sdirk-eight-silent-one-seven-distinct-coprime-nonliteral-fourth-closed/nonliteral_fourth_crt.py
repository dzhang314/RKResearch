"""Fast finite diagonal and height-bounded CRT for the j=4 tail/front resultant."""
from nonliteral_fourth_projection import *
from nonliteral_fourth_tight import tight_profiles as profiles,tightened as tail_pair
from flint import nmod_mpoly_ctx,nmod_poly
from math import lcm,factorial
from sympy import prevprime
from time import perf_counter

def int_rows(W):
 terms={};D=1
 for (i,j,k,l,m),a in W.to_dict().items():
  assert not (i or k)
  if m:a/=2
  D=lcm(D,int(a.q))
  if (j,l) not in terms:terms[j,l]=[Q(0),Q(0)]
  terms[j,l][m]=a
 out={e:[int(a*D) for a in v] for e,v in terms.items()}
 assert all(D*a==b for e,v in terms.items() for a,b in zip(v,out[e]))
 return out,sum(abs(a)+2*abs(b) for a,b in out.values()),D

@lru_cache(None)
def packed(f,i,r):
 F=profiles(f,i)[0];G=tail_pair(f,i,r)[0]
 A,a,dA=int_rows(F);B,b,dB=int_rows(G)
 m,n=F.degrees()[1],G.degrees()[1]
 N=m*G.degrees()[3]+n*F.degrees()[3]
 H=factorial(m+n)*a**n*b**m
 return A,B,m,n,N,H,dA,dB

@lru_cache(None)
def mp_ctx(p):
 return nmod_mpoly_ctx.get(['s','g'],modulus=p)

def resultant_mod(W,p,w):
 A,B,m,n,N,H,dA,dB=W
 C=mp_ctx(p)
 mk=lambda T:C.from_dict({e:(a+w*b)%p for e,(a,b) in T.items()})
 F,G=map(mk,(A,B))
 if F.degrees()[0]!=m or G.degrees()[0]!=n:return None
 R=F.resultant(G,0)
 assert not R or R.degrees()[0]==0
 X=[0]*(N+1)
 for (j,k),v in R.to_dict().items():
  assert not j and k<=N;X[k]=int(v)
 return nmod_poly(X,p)

def prime_seq():
 n=2**61
 while True:
  n=int(prevprime(n))
  if n%8==7:
   w=pow(2,(n+1)//4,n)
   assert w*w%n==2
   yield n,w

def reconstruct(f,i,r):
 W=packed(f,i,r);N,H=W[4:6]
 aa=[0]*(N+1);bb=aa[:];mm=1;j=0;st=perf_counter()
 for p,w in prime_seq():
  A,B=resultant_mod(W,p,w),resultant_mod(W,p,-w)
  if A is None or B is None:continue
  q=pow(mm,-1,p);sw=pow(2*w,-1,p);s2=pow(2,-1,p)
  a,b=[int(A[k]) for k in range(N+1)],[int(B[k]) for k in range(N+1)]
  aa=[c+mm*(((x+y)*s2-c)*q%p) for c,x,y in zip(aa,a,b)]
  bb=[c+mm*(((x-y)*sw-c)*q%p) for c,x,y in zip(bb,a,b)]
  mm*=p;j+=1
  if j%16==0 or j==1:print('j4 CRT',f,i,r,j,mm.bit_length(),H.bit_length(),round(perf_counter()-st,2),flush=True)
  if mm>2*H:
   ctr=lambda a:[x-mm if x*2>mm else x for x in a]
   aa=ctr(aa);bb=ctr(bb)
   assert max(map(abs,aa))<=H and max(map(abs,bb))<=H
   R=E(P(aa),P([2*x for x in bb]));assert R
   print('complete j4 padded projection',f,i,r,R.degree(),H.bit_length(),flush=True)
   return R
