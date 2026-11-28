"""Deterministic height-bounded exact reconstruction of the padded diagonal."""
from infinity_certificate import inputs,fixed_prem
from reduced_projection import Base,syl
from nofront_arith_cross import E,P,Q
from flint import nmod_poly
from sympy import prevprime
from itertools import product
from math import lcm,factorial
from time import perf_counter

def ap(x):
 return (int(x.p),int(x.q))
def flatten(A):
 return [p for row in A for p in row]

def height(A):
 d=1
 for r in A:
  for j in range(r.degree()+1):
   d=lcm(d,int(r.a[j].q),int((r.b[j]/2).q))
 V=[]
 for r in A:
  row=[]
  for j in range(r.degree()+1):
   a,b=r.a[j]*d,r.b[j]*d/2
   assert a.q==b.q==1
   row.append((int(a),int(b)))
  V.append(row)
 return d,sum(abs(a)+2*abs(b) for row in V for a,b in row),V

def reassemble(example,vec):
 V=iter(vec)
 return [[next(V) for _ in row] for row in example]

def packed(f,i):
 R,P0,J,dp,dj=inputs(f,i)
 rd,hr,rr=height(R);pd,hp,pp=height(flatten(P0));jd,hj,jj=height(flatten(J))
 rr,pp,jj=rr,reassemble(P0,pp),reassemble(J,jj)
 m,n=len(J)-1,len(P0)-1;D=3*m+27
 N=2040 if f else 2176
 H=factorial(D+5)*hr**D*(factorial(m+n)*hp**m*hj**n)**5
 return (rr,pp,jj,m,n,D,N,H),(rd,pd,jd)

def modular(W,p,w):
 R,Phi,J,m,n,D,degree,upper=W
 z=lambda V:nmod_poly([(a+w*b)%p for a,b in V],p)
 r=list(map(z,R))
 if r[-1].degree()!=6:return None
 U=Base(r,p)
 A=[U.mk(list(map(z,cs))) for cs in Phi]
 B=[U.mk(list(map(z,cs))) for cs in J]
 C=fixed_prem(B,A)
 K,V=U.norm(syl(A,C,U));L,X=U.norm(A[-1])
 if not K or not L:return None
 e=(n-1)+n*(m-n+1)-m
 k=D+X*e-V
 ell=U.ell
 N=L**e
 if k>=0:K=K*ell**k
 else:N=N*ell**(-k)
 f,r=divmod(K,N)
 assert not r
 if f.degree()!=degree:return None
 return f

def prime_seq():
 p=2**61
 while True:
  p=int(prevprime(p))
  if p%8==7:
   w=pow(2,(p+1)//4,p)
   assert w*w%p==2
   yield p,w

def rec(f,i):
 W,sc=packed(f,i);N,H=W[-2:]
 a=[0]*(N+1);b=[0]*(N+1);M=1;n=0;st=perf_counter()
 for p,w in prime_seq():
  A=modular(W,p,w);B=modular(W,p,-w)
  if A is None or B is None:continue
  p2=pow(2,-1,p)
  w2=pow(2*w,-1,p)
  mv=pow(M,-1,p)
  aa,bb=list(map(int,A)),list(map(int,B))
  a=[u+M*((((x+y)*p2-u)*mv)%p) for u,x,y in zip(a,aa,bb)]
  b=[u+M*((((x-y)*w2-u)*mv)%p) for u,x,y in zip(b,aa,bb)]
  M*=p;n+=1
  if n%16==0 or n==1:
   print('CRT exact norm progress',f,i,n,M.bit_length(),H.bit_length(),round(perf_counter()-st,2),flush=True)
  if M>2*H:
   a=[u-M if 2*u>M else u for u in a];b=[u-M if 2*u>M else u for u in b]
   assert max(map(abs,a))<=H and max(map(abs,b))<=H
   assert len(a)==len(b)==N+1 and (a[-1] or b[-1])
   print('exact no-front padded diagonal ready',f,i,'degree',N,'CRT bits',M.bit_length(),
         'coefficient bits',max(max(map(abs,a)).bit_length(),max(map(abs,b)).bit_length()),flush=True)
   return E(P(a),P([2*x for x in b]))

if __name__=='__main__':
 rec(True,0)
