"""Bounded exact coefficient pseudo-gcd; no inverses in the diagonal quotient."""
from exact_guard_cuts import prep,split_deg
from shared_arith_projection import *
from shared_silent8_projection import enorm

class SplitE(Exception):
 def __init__(self,Q):self.Q=Q

class Remainder:
 def __init__(self,M):
  self.M=M
  q=enorm(M)
  self.N=E(q/q[q.degree()])
 def coeff(self,a):return (a%self.N)%self.M if a.degree()>=self.M.degree() else a
 def trim(self,A):
  A=[self.coeff(a) for a in A]
  while A and not A[-1]:A.pop()
  return A
 def require_lc(self,A):
  D=egcd(self.M,A[-1])
  if D.degree()>0:
   assert D.degree()<self.M.degree()
   raise SplitE(D)
  return A[-1]
 def pseudo_div(self,A,B):
  assert B
  L=self.require_lc(B);z=[E(0)]*max(1,len(A)-len(B)+1)
  while len(A)>=len(B):
   k=len(A)-len(B);u=A[-1]
   z=self.trim([L*v+(u if i==k else E(0)) for i,v in enumerate(z+[E(0)]*max(0,k+1-len(z)))])
   A=self.trim([L*a-(B[j-k]*u if k<=j<k+len(B) else E(0)) for j,a in enumerate(A)])
  return z,A
 def gcd(self,A,B):
  while B:
   A,B=B,self.pseudo_div(A,B)[1]
  self.require_lc(A)
  return A

def pu(M,R,L0,L1,pr=True):
 P=Remainder(M)
 try:
  A=P.trim(R);assert A
  old=len(A)-1
  for B in (L0,L1):
   B=P.trim(B);assert B
   while len(A)>1:
    C=P.gcd(A,B)
    if len(C)<=1:break
    A,r=P.pseudo_div(A,C);assert not r and A
  P.require_lc(A)
  if len(A)==1:A=[E(1)]
  return [(unef(M),list(map(unef,A)),old)]
 except SplitE as e:
  X=e.Q
  if pr:print('exact diagonal pseudo split',M.degree(),X.degree(),flush=True)
  return pu(X,R,L0,L1,pr)+pu(eexact(M,X).monic(),R,L0,L1,pr)

@lru_cache(None)
def fast_cuts(f,i):
 S,G,R,L0,L1=prep(f,i)
 reg=[(A,R[:n+1],n) for A,n in split_deg(S,R)]
 spec=[]
 re=list(map(ef,R));la=list(map(ef,L0));lb=list(map(ef,L1))
 for A in G:spec+=pu(ef(A),re,la,lb)
 print('fast exact u branch structure',f,i,[(len(A)-1,len(W)-1,n) for A,W,n in spec],
       [(len(A)-1,len(W)-1,n) for A,W,n in reg],flush=True)
 return spec+reg
