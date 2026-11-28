"""First/fifth pure projection in the exact degree-five arithmetic tail quotient."""
from nofront_arith_tails import tail,guards,e_sf
from shared_arith_projection import bareiss,coefficients_e
from no_extra import *
from literal_shared_pole_front import frontdata,exact_uc_y
from shared_silent8_projection import ef,unef,egcd,eguard,epow,etry,eexact
from flint import fmpq_mpoly_ctx
from itertools import product

CX=fmpq_mpoly_ctx.get(['y','s','u','g','t'])
y,s,u,g,t=CX.gens()
LT=t*t-CX.constant(Q(1)/2)
def fold(M):
 if isinstance(M,int):M=CX.constant(M)
 return M%LT
def div(M,D):
 q,r=divmod(M,D);return fold(q),fold(r)
def exdiv(M,D):
 q,r=div(M,D);assert not r
 return q
def C(v):
 z=F2(v).v
 return z.a[0]+t*z.b[0]
def term(V,x):return sum(C(a)*x**j for j,a in enumerate(V))
def ats(F):
 return fold(sum(a*s**(i+j)*u**k*g**l*t**m for (i,j,k,l,m),a in F.to_dict().items()))
def conv(F):
 return CX.from_dict({(0,*j):a for j,a in F.to_dict().items()})
L=lambda x:sum(v*x**j for j,v in enumerate(Lco))

@lru_cache(None)
def fronts(f,i):
 A,B,m,ha,hb,a,b,hh,H4,L0,e,tau,ah,HS,XT,XA,DT,DA,*_=frontdata(f,i)
 R,q0,q1,gg=tail(f,i)
 A,B,a=map(C,(A,B,a));q0,q1=map(conv,(q0,q1))
 Qs=lambda Y:fold(q0+q1*g*Y)
 H=term(H4,s);Q0=fold(L(g*a)*Qs(y));P=fold(C(hh)*Qs(a)*L(g*y))
 Phi=exdiv(fold(H*ats(Q0)-ats(P)),s-a)
 m0=y-1;m1=y*y/2-y;m2=y**3/3-y*y
 J=m2-(A+B)*m1+A*B*m0
 T0=fold(y**3-y**4/4+(A+B)*m2-A*B*m1+s*J)
 A0=fold(C(L0[0])*m0+C(L0[1])*m1+term(e,s)*J)
 T1=fold(H*(term(DT,s)-C(tau))-term(exact_uc_y(XT),s)*(y-a))
 A1=fold(H*(term(DA,s)-C(ah))-term(exact_uc_y(XA),s)*(y-a))
 FT=exdiv(fold(H*T0*Q0+T1*P),y-a);FA=exdiv(fold(H*A0*Q0+A1*P),y-a)
 FT,FTR=div(FT,y-s);FA,FAR=div(FA,y-s)
 assert not fold(FTR-ats(T0)*Phi) and not fold(FAR-ats(A0)*Phi)
 E=fold(T0*A1-A0*T1)
 E=exdiv(exdiv(E,y-a),y-s)
 assert E.degrees()==(3,3,0,0,1)
 print("literal cross degrees",f,i,E.degrees(),flush=True)
 return Phi,FT,FA,E

def E_su(F):
 B={}
 for (i,j,k,l,m),a in fold(F).to_dict().items():
  assert not i
  D=B.setdefault(j,{}).setdefault(k,[{},{}])[m]
  D[l]=D.get(l,Q(0))+a
 def p(d):return P([d.get(k,Q(0)) for k in range(max(d,default=-1)+1)])
 S=[]
 for j in range(max(B,default=-1)+1):
  A=B.get(j,{})
  S.append([E(*map(p,A.get(k,[{},{}]))) for k in range(max(A,default=-1)+1)])
 return S

def ptrim(a):
 while a and not a[-1]:a=a[:-1]
 return a
def coeffs_u(a,k):return a[k] if k<len(a) else E(0)

class UContext:
 def __init__(self,X):
  self.R=ptrim(X);self.n=len(self.R)-1;assert self.n==5
  self.lc=self.R[-1]
 @lru_cache(None)
 def power(self,j):
  if not j:return E(1)
  if j==1:return self.lc
  return epow(self.lc,j)
 def e(self,A,m=0):
  A=ptrim(A)
  while len(A)>self.n:
   v=A[-1];j=len(A)-len(self.R)
   A=ptrim([w*self.lc-(self.R[k-j]*v if j<=k<j+len(self.R) else E(0)) for k,w in enumerate(A)])
   m+=1
  return UElem(self,A,m)
 def unit(self,i):return self.e([E(i)])
 def norm_numerator(self,a):
  n=self.n
  Z=[self.e([E(0)]*j+a.x,a.n) for j in range(n)]
  # Each column can be independently multiplied by a nonzero LC power.
  X=[[coeffs_u(b.x,i) for b in Z] for i in range(n)]
  return bareiss(X),[b.n for b in Z]

class UElem:
 def __init__(self,F,x,n):self.F,self.x,self.n=F,x,n
 def __bool__(self):return bool(self.x)
 def cv(self,v):return self.F.unit(v) if isinstance(v,int) else v
 def __add__(self,w):
  w=self.cv(w);F=self.F
  if not w:return self
  if not self:return w
  n=max(self.n,w.n);a,b=F.power(n-self.n),F.power(n-w.n)
  return F.e([coeffs_u(self.x,j)*a+coeffs_u(w.x,j)*b for j in range(max(len(self.x),len(w.x)))],n)
 __radd__=__add__
 def __neg__(self):return self.F.e([-a for a in self.x],self.n)
 def __sub__(self,w):return self+-self.cv(w)
 def __rsub__(self,w):return self.cv(w)+-self
 def __mul__(self,w):
  w=self.cv(w);F=self.F
  if not self or not w:return F.unit(0)
  Z=[E(0)]*(len(self.x)+len(w.x)-1)
  for i,a in enumerate(self.x):
   if a:
    for j,b in enumerate(w.x):
     if b:Z[i+j]+=a*b
  return F.e(Z,self.n+w.n)
 __rmul__=__mul__

def prem_s(A,B):
 l=B[-1]
 while len(A)>=len(B):
  k=len(A)-len(B);a=A[-1]
  A=ptrim([v*l-(B[j-k]*a if k<=j<k+len(B) else 0) for j,v in enumerate(A)])
 return A

def resultant(A,B,context):
 m,n=len(A)-1,len(B)-1
 M=[[context.unit(0)]*(m+n) for _ in range(m+n)]
 for i in range(n):M[i][i:i+m+1]=A[::-1]
 for i in range(m):M[i+n][i:i+n+1]=B[::-1]
 return det(M)
