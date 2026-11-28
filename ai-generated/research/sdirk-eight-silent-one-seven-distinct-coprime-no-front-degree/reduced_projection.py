"""Compute the exact projector's full reduced coefficients without expanding Q(t)[g]."""
from infinity_certificate import inputs,fixed_prem,det_sparse
from check_degree import leading
from shared_silent8_projection import red_e
from flint import nmod_poly
from functools import lru_cache
from itertools import product

def trim(A):
 while A and not A[-1]:A=A[:-1]
 return A

class Base:
 def __init__(self,pol,p):
  self.R=pol;self.ell=pol[-1];assert len(pol)==6 and self.ell
  self.p=p
 def pol(self,k):return nmod_poly([k],self.p)
 @lru_cache(None)
 def power(self,i):return self.ell**i
 def cv(self,i):return self.mk([self.pol(i)])
 def mk(self,A,m=0):
  A=trim(A)
  while len(A)>5:
   k=len(A)-6;a=A[-1]
   A=trim([b*self.ell-(a*self.R[j-k] if k<=j<k+6 else 0)
            for j,b in enumerate(A)])
   m+=1
  return V(self,A,m)
 def norm(self,a):
  n=5
  M=[self.mk([self.pol(0)]*j+a.x,a.n) for j in range(n)]
  return bareiss([[A.x[i] if i<len(A.x) else self.pol(0) for A in M] for i in range(n)],self.p),sum(A.n for A in M)

class V:
 def __init__(self,F,x,n):self.F,self.x,self.n=F,x,n
 def coerce(self,o):return self.F.cv(o) if isinstance(o,int) else o
 def __bool__(self):return bool(self.x)
 def __neg__(self):return V(self.F,[-x for x in self.x],self.n)
 def __add__(self,o):
  o=self.coerce(o);F=self.F
  if not self:return o
  if not o:return self
  k=max(self.n,o.n);a,b=F.power(k-self.n),F.power(k-o.n)
  return F.mk([(self.x[j]*a if j<len(self.x) else 0)+(o.x[j]*b if j<len(o.x) else 0)
                for j in range(max(len(self.x),len(o.x)))],k)
 __radd__=__add__
 def __sub__(self,o):return self+-self.coerce(o)
 def __rsub__(self,o):return self.coerce(o)+-self
 def __mul__(self,o):
  o=self.coerce(o);F=self.F
  if not self or not o:return F.cv(0)
  A=[F.pol(0)]*(len(self.x)+len(o.x)-1)
  for i,v in enumerate(self.x):
   if v:
    for j,w in enumerate(o.x):
     if w:A[i+j]+=v*w
  return F.mk(A,self.n+o.n)
 __rmul__=__mul__

def bareiss(M,p):
 n=len(M);sg=1;o=nmod_poly([1],p)
 M=[list(a) for a in M]
 for k in range(n-1):
  if not M[k][k]:
   j=next((u for u in range(k+1,n) if M[u][k]),None)
   if j is None:return nmod_poly([],p)
   M[k],M[j]=M[j],M[k];sg=-sg
  a=M[k][k]
  for i in range(k+1,n):
   for j in range(k+1,n):
    v,q=divmod(a*M[i][j]-M[i][k]*M[k][j],o)
    assert not q;M[i][j]=v
   M[i][k]=nmod_poly([],p)
  o=a
 return sg*M[-1][-1]

def syl(A,B,T):
 m,n=len(A)-1,len(B)-1
 M=[[T.cv(0)]*(m+n) for _ in range(m+n)]
 for i in range(n):M[i][i:i+m+1]=A[::-1]
 for i in range(m):M[i+n][i:i+n+1]=B[::-1]
 return det_sparse(M,T.cv)

@lru_cache(None)
def reduced(f,i,p,t):
 R,Ph,J,dp,dj=inputs(f,i)
 z=lambda a:red_e(a,p,t)
 T=Base(list(map(z,R)),p)
 A=[T.mk(list(map(z,cs))) for cs in Ph]
 B=[T.mk(list(map(z,cs))) for cs in J]
 C=fixed_prem(B,A)
 N,de=T.norm(syl(A,C,T));L,el=T.norm(A[-1])
 assert N and L
 m,n=len(B)-1,len(A)-1
 s_power=(n-1)+n*(m-n+1)-m
 ell_power=3*m+27+el*s_power-de
 W=L**s_power
 if ell_power>=0:N=N*T.power(ell_power)
 else:W=W*T.power(-ell_power)
 Y,r=divmod(N,W);assert not r
 assert Y.degree()==(2040 if f else 2176)
 assert int(Y.leading_coefficient())=={(True,0):808,(True,1):318,(False,0):616,(False,1):195}[f,i]
 print('full reduced no-front projection:',f,i,p,Y.degree(),len(Y.factor()[1]),flush=True)
 return Y

if __name__=='__main__':
 for f,i in product((True,False),(0,1)):reduced(f,i,1103,161)
