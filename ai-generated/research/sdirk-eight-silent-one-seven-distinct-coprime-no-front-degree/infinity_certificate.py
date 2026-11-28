"""Truncated series at γ=infinity for the exact unexpanded no-front norm."""
from nofront_arith_cross import *
from functools import lru_cache
from flint import nmod_poly

class Base:
 def __init__(self,N,p=0,t=0):self.N,self.p,self.t=N,p,t
 def slice(self,a,k=None):
  if k is None:k=self.N
  return a.truncate(k) if self.p else E(a.a.truncate(k),a.b.truncate(k))
 def cv(self,n):return BVal(self,nmod_poly([n],self.p) if self.p else E(n))
 def at_infinity(self,a,d):
  n=min(self.N,d+1)
  if self.p:
   def v(c):return int(c.p)*pow(int(c.q),-1,self.p)
   b=nmod_poly([(v(a.a[d-j])+self.t*v(a.b[d-j]))%self.p for j in range(n)],self.p)
  else:
   b=E(P([a.a[d-j] for j in range(n)]),P([a.b[d-j] for j in range(n)]))
  return BVal(self,b)
 def inv(self,x):
  a=x.x
  if self.p:return BVal(self,a.inverse_series_trunc(self.N))
  n=(a.a*a.a-a.b*a.b/2).truncate(self.N)
  z=P([1/n[0]]);k=1
  while k<self.N:
   k=min(2*k,self.N);z=(z*(2-n*z)).truncate(k)
  return BVal(self,self.slice(E(a.a*z,-a.b*z)))
 def val(self,x):
  if self.p:return next((j for j in range(self.N) if x.x[j]),self.N)
  return next((j for j in range(self.N) if x.x.a[j] or x.x.b[j]),self.N)
 def scalar(self,x,j):
  if self.p:return int(x.x[j])
  return E(x.x.a[j],x.x.b[j])

class BVal:
 def __init__(self,F,x):self.F,self.x=F,x
 def cv(self,a):return self.F.cv(a) if isinstance(a,int) else a
 def __bool__(self):return bool(self.x)
 def __add__(self,a):return BVal(self.F,self.x+self.cv(a).x)
 __radd__=__add__
 def __neg__(self):return BVal(self.F,-self.x)
 def __sub__(self,a):return self+-self.cv(a)
 def __rsub__(self,a):return self.cv(a)+-self
 def __mul__(self,a):return BVal(self.F,self.F.slice(self.x*self.cv(a).x))
 __rmul__=__mul__

class Tail:
 def __init__(self,B,R):
  self.B=B;den=B.inv(R[-1]);self.R=[a*den for a in R];self.n=len(R)-1
 def cv(self,k):return UVal(self,[self.B.cv(k)])
 def mk(self,A):
  A=ptrim(A)
  while len(A)>self.n:
   k=len(A)-len(self.R);a=A[-1]
   A=ptrim([b-(self.R[j-k]*a if k<=j<k+len(self.R) else self.B.cv(0))
            for j,b in enumerate(A)])
  return UVal(self,A)
 def norm(self,a):
  n=self.n
  A=[self.mk([self.B.cv(0)]*j+a.x).x for j in range(n)]
  M=[[v[i] if i<len(v) else self.B.cv(0) for v in A] for i in range(n)]
  return det_sparse(M,self.B.cv)

class UVal:
 def __init__(self,T,x):self.T,self.x=T,ptrim(x)
 def cv(self,a):return self.T.cv(a) if isinstance(a,int) else a
 def __bool__(self):return bool(self.x)
 def __add__(self,a):
  a=self.cv(a);B=self.T.B
  return UVal(self.T,[(self.x[j] if j<len(self.x) else B.cv(0))+
                      (a.x[j] if j<len(a.x) else B.cv(0))
                       for j in range(max(len(self.x),len(a.x)))])
 __radd__=__add__
 def __neg__(self):return UVal(self.T,[-a for a in self.x])
 def __sub__(self,a):return self+-self.cv(a)
 def __rsub__(self,a):return self.cv(a)+-self
 def __mul__(self,a):
  a=self.cv(a);T=self.T
  if not self or not a:return T.cv(0)
  z=[T.B.cv(0)]*(len(self.x)+len(a.x)-1)
  for j,v in enumerate(self.x):
   if v:
    for k,w in enumerate(a.x):
     if w:z[j+k]+=v*w
  return T.mk(z)
 __rmul__=__mul__

def det_sparse(M,cv):
 n=len(M);row=sorted(range(n),key=lambda i:sum(map(bool,M[i])))
 sg=(-1)**sum(row[a]>row[b] for a in range(n) for b in range(a+1,n))
 @lru_cache(None)
 def f(i,mask):
  if not mask:return cv(1)
  v=cv(0);s=1
  for j in range(n):
   if mask>>j&1:
    if M[row[i]][j]:
     q=f(i+1,mask^(1<<j))
     if q:v+=s*M[row[i]][j]*q
    s=-s
  return v
 return sg*f(0,(1<<n)-1)

def syl(A,B,T):
 m,n=len(A)-1,len(B)-1
 M=[[T.cv(0)]*(m+n) for _ in range(m+n)]
 for i in range(n):M[i][i:i+m+1]=A[::-1]
 for i in range(m):M[i+n][i:i+n+1]=B[::-1]
 return det_sparse(M,T.cv)

def fixed_prem(A,B):
 # Use the full nominal degree in s even on truncated zeros.
 n=len(B)-1;L=B[-1]
 for d in range(len(A)-1,n-1,-1):
  k=d-n;a=A[d]
  Q=[c*L-(B[j-k]*a if k<=j<k+len(B) else 0) for j,c in enumerate(A)]
  assert not Q[-1]
  A=Q[:-1]
 return A

@lru_cache(None)
def inputs(f,i):
 Ph,T,A,D=fronts(f,i)
 R,q0,q1,safe=tail(f,i)
 J=fold(T.resultant(D,0))
 return coefficients_e(R),E_su(Ph),E_su(J),Ph.degrees()[3],J.degrees()[3]

def run(f,i,depth,p=0,t=0):
 R,Ph,J,dp,dj=inputs(f,i)
 dr=max(a.degree() for a in R)
 assert dr==R[-1].degree()
 B=Base(depth,p,t);T=Tail(B,[B.at_infinity(a,dr) for a in R])
 P=[T.mk([B.at_infinity(a,dp) for a in cols]) for cols in Ph]
 Q=[T.mk([B.at_infinity(a,dj) for a in cols]) for cols in J]
 Z=fixed_prem(Q,P)
 K=T.norm(syl(P,Z,T));L=T.norm(P[-1])
 ek,el=B.val(K),B.val(L)
 m,n=len(Q)-1,len(P)-1
 e=(n-1)+n*(m-n+1)-m
 if ek==depth or el==depth:
  print('short infinity window',f,i,p,depth,ek,el,flush=True)
  return None
 h=5*(dp*m+dj*n)-ek+e*el
 cK,cL=B.scalar(K,ek),B.scalar(L,el)
 print('degree preserving infinity outcome',f,i,p,depth,'raw valuations',ek,el,'H degree',h,
       'denominator exponent upper',5*(3*m+27),flush=True)
 return (h,cK,cL,e)

if __name__=='__main__':
 for f,i in product((True,False),(0,1)):run(f,i,96,1103,161)
