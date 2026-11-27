"""Exact line-pole row-five exclusion with a finite-quotient modular unit test."""
from check_seven_sites import *

def bareiss(A):
 n=len(A)
 if n==0:return one
 d=one;sign=1
 A=[list(row) for row in A]
 for i in range(n-1):
  if not A[i][i]:
   pivot=next((r for r in range(i+1,n) if A[r][i]),None)
   if pivot is None:return zero
   A[i],A[pivot]=A[pivot],A[i];sign=-sign
  D=A[i][i]
  for r in range(i+1,n):
   for c in range(i+1,n):
    A[r][c]=(D*A[r][c]-A[r][i]*A[i][c]).exact(d)
   A[r][i]=zero
  d=D
 return A[-1][-1]*sign
def sylvester(f,g):
 m=len(f)-1;n=len(g)-1
 C=[[zero]*(i)+f[::-1]+[zero]*(n-1-i) for i in range(n)]
 D=[[zero]*(i)+g[::-1]+[zero]*(m-1-i) for i in range(m)]
 return C+D
def result(f,g):return bareiss(sylvester(f,g))

from flint import nmod_poly
from math import isqrt

def strip_content(polys, guards):
 for q in guards:
  while q.degree()>0:
   d=q.gcd(polys[-1])
   for fr in polys[:-1]:
    if d.degree()==0:break
    d=d.gcd(fr)
   if d.degree()==0:break
   polys=[u.exact(d) for u in polys]
 return polys

def linear_combination_polynomials(f,q):
 # Shifts X^i f, i=0…2; X^i q, i=0…3.
 cols=[xmul(f,i) for i in range(3)]+[xmul(q,i) for i in range(4)]
 def row(k):return [p[k] if len(p)>k else zero for p in cols]
 R=[row(i) for i in range(2,8)]
 return bareiss(R+[row(1)]),bareiss(R+[row(0)])

def mod_q(x,p):
 return int(x.p)%p*pow(int(x.q),-1,p)%p
def cast(x,p,t0):
 return nmod_poly([(mod_q(x.a[j],p)+t0*mod_q(x.b[j],p))%p
                   for j in range(x.degree()+1)],p)
class NotUnit(Exception):pass
class MField:
 def __init__(self,p,t,M):
  self.p=p;self.t=t;self.M=cast(M,p,t)
  assert self.M.degree()==M.degree() and int(self.M.leading_coefficient())==1
 def of(self,a):
  if isinstance(a,ME):
   assert a.f is self
   return a
  if isinstance(a,nmod_poly):return ME(a%self.M,self)
  return ME(cast(E.cast(a),self.p,self.t)%self.M,self)
class ME:
 def __init__(self,x,f):self.x=x;self.f=f
 def av(self,a):return self.f.of(a)
 def __bool__(self):return bool(self.x)
 def __eq__(self,a):return self.x==self.av(a).x
 def __add__(self,a):return self.av(self.x+self.av(a).x)
 __radd__=__add__
 def __neg__(self):return self.av(-self.x)
 def __sub__(self,a):return self+-self.av(a)
 def __rsub__(self,a):return self.av(a)+-self
 def __mul__(self,a):return self.av(self.x*self.av(a).x)
 __rmul__=__mul__
 def inv(self):
  h,i,_=self.x.xgcd(self.f.M)
  if h.degree()!=0:raise NotUnit()
  V=self.av(i)
  assert self*V==1
  return V
 def __truediv__(self,a):return self*self.av(a).inv()
 def __rtruediv__(self,a):return self.av(a)*self.inv()
 def __pow__(self,n):
  y=self.av(1)
  for _ in range(n):y*=self
  return y

# Helpers generic enough for the finite coefficient algebra.
def pmul(f,g):
 h=[0]*(len(f)+len(g)-1)
 for i,x in enumerate(f):
  for j,y in enumerate(g):h[i+j]+=x*y
 return clean(h)
def pmval(f,x):
 r=0
 for a in f[::-1]:r=r*x+a
 return r
def monicqr(f,q):
 assert q[-1]==1
 f=clean(f);b=[0]*max(0,len(f)-len(q)+1)
 while f and len(f)>=len(q):
  d=len(f)-len(q);v=f[-1];b[d]=v
  for j,c in enumerate(q):f[d+j]-=v*c
  f=clean(f)
 return clean(b),f
def timesprod(x):
 a=1
 for u in x:a*=u
 return a
def md(M):
 n=len(M)
 return sum((-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))*
            timesprod(M[i][p[i]] for i in range(n)) for p in permutations(range(n)))
def crt(M,b):
 n=len(M)
 return [md([[b[i] if j==k else M[i][j] for j in range(n)] for i in range(n)]) for k in range(n)]

def gates(front,source,s,r):
 Z,O,gg,gg1,la=r(0),r(1),r(g),r(g1),r(E(2)/3)
 a,b,ha,hb,p,delta,tap,tapd=source
 a,b,ha,hb,delta=map(r,(a,b,ha,hb,delta))
 p=[r(v) for v in p];xi=r(z)
 u=r(1+2*t); w=2-u if front else 2*u
 aa=Z if front else 3*u/2-1
 u21,u31,u32=gg*u,gg*(w-aa),gg*aa
 assert ha==gg1*u21 and hb==gg1*u31
 tapr=[[r(x) for x in row] for row in tap]
 dtap=md(tapr)
 qr=[i/dtap for i in crt(tapr,[s-gg,s*s/2-gg*s,s**3/3-gg*s*s])]
 hs=gg1*qr[0]
 assert pmval(p,s)==delta*(s-xi)*hs
 AH=(gg*ha,u32*ha+gg*hb,qr[1]*ha+qr[2]*hb+gg*hs)
 def tau(c,T,C):return gg*c**3+sum(u*v**3 for u,v in zip(T,C))-c**4/4
 TA=(tau(a,[u21],[gg]),tau(b,[u31,u32],[gg,a]),tau(s,qr,[gg,a,b]))
 def L4(x):return 70*x**4-140*x**3+90*x*x-20*x+1
 l=[O,-20*O,90*O,-140*O,70*O]
 D=[-delta*xi,delta];T1=scale(p,O/gg1)
 m0=add(pmul(D,[-gg,O]),scale(T1,-O))
 m1=add(pmul(D,[Z,-gg,O/2]),scale(T1,-gg))
 m2=add(add(pmul(D,[Z,Z,-gg,O/3]),scale(p,la)),scale(T1,-gg**2))
 V=(a-b)*(a-s)*(b-s)
 V.inv() # invariant on the entire retained fiber
 def filt(c,d):return add(add(m2,scale(m1,-c-d)),scale(m0,c*d))
 MA=scale(filt(b,s),b-s);MB=scale(filt(a,s),s-a);MS=scale(filt(a,b),a-b)
 YA=add(add(scale(p,gg*V),scale(MA,ha)),add(scale(MB,hb),scale(MS,hs)))
 YT=add(add(scale(pmul([Z,Z,Z,gg,-O/4],D),V),scale(T1,gg**3*V)),
        add(add(scale(MA,a**3),scale(MB,b**3)),scale(MS,s**3)))
 ret=[]
 for f0,f1 in ((AH,YA),(TA,YT)):
  C=[[ha,a*ha,L4(a),f0[0]],[hb,b*hb,L4(b),f0[1]],[hs,s*hs,L4(s),f0[2]]]
  ans=[]
  for j,k in enumerate((scale(p,V),[Z]+scale(p,V),scale(pmul(l,D),V),f1)):
   co=md([[row[i] for i in range(4) if i!=j] for row in C])
   ans=add(ans,scale(k,(-1)**(3+j)*co))
  ret.append(ans)
 return ret

def invertible_action(Q,F):
 # Dvd elimination via multiplication in the monic Q quotient, so
 # a possible degree drop of F mod p does not invalidate the certificate.
 n=len(Q)-1
 col=[monicqr([0]*j+F,Q)[1] for j in range(n)]
 a=Q[-1].av(0)
 A=[[col[j][i] if len(col[j])>i else a for j in range(n)] for i in range(n)]
 try:md(A).inv()
 except NotUnit:return False
 return True

def check(front,source,F,Q,M,A,B):
 p,root=1009,285
 assert all(p%k for k in range(2,isqrt(p)+1))
 assert (2*root*root-1)%p==0
 f=MField(p,root,M);r=f.of
 s=-r(B)/r(A)
 Q0=[r(x)/r(Q[-1]) for x in Q]
 q,R=monicqr(Q0,[-s,r(1)])
 assert not R and len(q)==4
 g1,_=gates(front,source,s,r)
 assert invertible_action(q,g1)
 return p,root,1

def phase(front,rear,sign):
 F,T,G,c,d,aux=data(front,rear,sign)
 H4=[[T[i+j] for j in range(4)] for i in range(4)]
 d4=det(H4);Qc=cramer(H4,[-T[4+i] for i in range(4)])+[d4]
 a,b,ha,hb,p,delta,*_=aux
 gd=(delta,p[-1],ev(p,z),z-a,z-b,z-c,z-d)
 Qc=strip_content(Qc,gd);F=strip_content(F,gd)
 R=result(F,Qc)
 S=R
 for scalar in [*gd,Qc[-1]]: S=strip(S,scalar)
 S=S.exact(S.gcd(S.der())).monic()
 A,B=linear_combination_polynomials(F,Qc)
 assert A
 print("phase",front,rear,sign,"primitive res",R.degree(),"squarefree",S.degree(),
       "subres lc guard deg",S.gcd(A).degree(),flush=True)
 assert S.gcd(A).degree()==0
 a,b,*_=aux
 known=(A*a+B)*(A*b+B)
 strip_s=strip(S,known)
 print("  removed twin fibers",S.degree()-strip_s.degree(),"remaining",strip_s.degree(),flush=True)
 return check(front,aux,F,Qc,strip_s,A,B)

if __name__=='__main__':
 import sys
 for front,rear,sig in product((True,False),(True,False),(1,-1)):
  if rear and sig==-1:continue
  if len(sys.argv)>1 and int(sys.argv[1])!=int(front):continue
  if len(sys.argv)>2 and int(sys.argv[2])!=int(rear):continue
  if len(sys.argv)>3 and int(sys.argv[3])!=sig:continue
  print(" unit receipt",phase(front,rear,sig),flush=True)
