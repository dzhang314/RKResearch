#!/usr/bin/env python3
from flint import fq_default_ctx,fq_default_poly_ctx,nmod_poly
from itertools import product,combinations
from math import lcm

def make_matrix(F,R,T,xs,bs):
 O=F.one();Z=F.zero();ga=O/2
 Promote=lambda x:R([x]) if not hasattr(x,'degree') else x
 xs,bs=[Promote(x) for x in xs],[Promote(b) for b in bs]
 I=lambda P:sum((a/(i+1) for i,a in enumerate(P.coeffs())),Z)
 def J(P):return R([Z]+[a/(i+1) for i,a in enumerate(P.coeffs())])
 def ev(P,x):return sum((a*x**i for i,a in enumerate(P.coeffs())),R.zero())
 r=T-ga;rr=[x-ga for x in xs];ix=[(i,j) for i in range(5) for j in range(i)];M=[]
 def add(f,v,ref):
  M.append([Promote(f[i])*Promote(v[j]) for i,j in ix]+
   [Promote(ref)-ga*sum((Promote(q)*Promote(t) for q,t in zip(f,v)),R.zero())])
 for i in range(5):
  e=[O if k==i else Z for k in range(5)]
  add(e,rr,ev(J(r),xs[i]))
  add([b*x for x,b in zip(rr,bs)],e,bs[i]*(I(r)-ev(J(r),xs[i])))
 for i in range(1,6):
  for j in range(1,7-i):
   add([b*x**i for x,b in zip(rr,bs)],[x**j for x in rr],I(r**i*J(r**j)))
 return M

def generic(R,T,M,forbidden):
 O=R.one();Z=R.zero()
 def canon(n,d):
  if n.is_zero():return Z,O
  g=n.gcd(d)
  return n//g,d//g
 def mul(a,b):return canon(a[0]*b[0],a[1]*b[1])
 def sub(a,b):return canon(a[0]*b[1]-a[1]*b[0],a[1]*b[1])
 def div(a,b):return canon(a[0]*b[1],a[1]*b[0])
 P={};Pivs=O;G=Z;bad=False
 for row in M:
  A=[(x,O) for x in row]
  for i in range(10):
   if A[i][0].is_zero():continue
   if i in P:
    a=A[i]
    A=[sub(x,mul(a,y)) for x,y in zip(A,P[i])]
   else:
    Pivs*=A[i][0]*A[i][1]
    P[i]=[div(x,A[i]) for x in A]
    break
  else:
   if not A[-1][0].is_zero():
    bad=True
    G=G.gcd(A[-1][0])
    Pivs*=A[-1][1]
 if not bad:return ('generically consistent',len(P))
 H=G*Pivs
 if H.degree()<=0:return []
 S=[]
 for q,e in H.factor()[1]:
  if not (forbidden%q).is_zero():
   pvs={};inconsistent=False
   for row in M:
    A=[x%q for x in row]
    for i in range(10):
     if A[i].is_zero():continue
     if i in pvs:
      a=A[i]
      A=[(x-a*y)%q for x,y in zip(A,pvs[i])]
     else:
      inv=A[i].inverse_mod(q)
      pvs[i]=[(x*inv)%q for x in A]
      break
    else:
     if not A[-1].is_zero():
      inconsistent=True
      break
   if not inconsistent:S.append((q,len(pvs)))
 return S

for p in (19,23):
 count=0
 F=fq_default_ctx(p,lcm(*(f.degree() for f,m in nmod_poly([-1,-2,1],p).factor()[1])),'u')
 R=fq_default_poly_ctx(F);T=R.gen();O=F.one();Z=F.zero()
 roots=[x for x,e in (T*T-2*T-1).roots()]
 I=lambda P:sum((a/(i+1) for i,a in enumerate(P.coeffs())),Z)
 for u,v in product(roots,repeat=2):
  a=(1+u)/2;b=(3-u)/2 if p==19 else (1+2*u)/2
  c=(1-v)/2;d=(v-1)/2 if p==19 else (1-2*v)/2
  xs=[O/2,a,b,d,c];P=R.one()
  for x in xs:P=P*(T-x)
  if any(I(T**i*P)!=0 for i in range(3)):continue
  assert all(x!=y for x,y in combinations(xs,2))
  ws=[]
  for i,x in enumerate(xs):
   P0=R.one()
   for j,y in enumerate(xs):
    if j!=i:P0=P0*(T-y)/(x-y)
   ws.append(I(P0))
  assert all(sum((w*x**i for w,x in zip(ws,xs)),Z)==O/(i+1) for i in range(8))
  X=[a,b,T,d,c];B=[ws[1],ws[2],Z,ws[3],ws[4]]
  m=make_matrix(F,R,T,X,B)
  assert generic(R,T,m,P)==[]
  count+=1
  for k in range(5):
   X=[a,b,xs[k],d,c];B=[R([ws[1]]),R([ws[2]]),T,R([ws[3]]),R([ws[4]])]
   if k:B[{1:0,2:1,3:3,4:4}[k]]-=T
   guard=B[3]*B[4]
   m=make_matrix(F,R,T,X,B)
   assert not guard.is_zero()
   assert generic(R,T,m,guard)==[]
   count+=1
 assert count=={19:24,23:6}[p]
 print(p,count,'entire one-parameter charts inconsistent')
