"""Exact height-bounded diagonal from the two bivariate fifth projections."""
from star_fifth import *
from nonliteral_fourth_crt import int_rows,resultant_mod,prime_seq
from math import factorial
from time import perf_counter

@lru_cache(None)
def data(f,i,kind='star'):
 assert kind=='star'
 P,Q0,*_=star(f,i)
 A,a,dA=int_rows(P);B,b,dB=int_rows(Q0)
 m,n=P.degrees()[1],Q0.degrees()[1]
 N=m*Q0.degrees()[3]+n*P.degrees()[3]
 H=factorial(m+n)*a**n*b**m
 return A,B,m,n,N,H,dA,dB

def rec(f,i,kind='star'):
 W=data(f,i,kind);N,H=W[4:6]
 aa=[0]*(N+1);bb=list(aa);mm=1;j=0;st=perf_counter()
 for p,w in prime_seq():
  A,B=resultant_mod(W,p,w),resultant_mod(W,p,-w)
  if A is None or B is None:continue
  q=pow(mm,-1,p);sw=pow(2*w,-1,p);s2=pow(2,-1,p)
  a,b=[int(A[k]) for k in range(N+1)],[int(B[k]) for k in range(N+1)]
  aa=[c+mm*(((x+y)*s2-c)*q%p) for c,x,y in zip(aa,a,b)]
  bb=[c+mm*(((x-y)*sw-c)*q%p) for c,x,y in zip(bb,a,b)]
  mm*=p;j+=1
  if j%16==0 or j==1:print('j5 CRT',f,i,kind,j,mm.bit_length(),H.bit_length(),round(perf_counter()-st,2),flush=True)
  if mm>2*H:
   ctr=lambda a:[x-mm if x*2>mm else x for x in a]
   aa=ctr(aa);bb=ctr(bb)
   assert max(map(abs,aa))<=H and max(map(abs,bb))<=H
   R=E(P(aa),P([2*x for x in bb]));assert R
   print('complete j5 scalar diagonal',f,i,kind,R.degree(),H.bit_length(),flush=True)
   return R
