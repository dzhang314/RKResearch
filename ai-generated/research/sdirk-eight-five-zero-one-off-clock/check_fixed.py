#!/usr/bin/env python3
from flint import fq_default_ctx,fq_default_poly_ctx,nmod_poly
from itertools import product,combinations
from math import lcm,isqrt
def fail(F,T,n):
 P={};ix=[]
 for j,A in enumerate(T):
  A=list(A)
  for i in range(n):
   t=A[i]
   if t==0:continue
   if i in P:A=[x-t*s for x,s in zip(A,P[i])]
   else:P[i]=[x/t for x in A];ix.append(j);break
  else:
   if A[-1]!=0:return len(P),j,A[-1],ix+[j]
 return len(P),None,None,ix
def block(F,R,X,xs,bs,ga=None):
 O=F.one();Z=F.zero()
 if ga is None:ga=O/2
 I=lambda P:sum((a/(i+1) for i,a in enumerate(P.coeffs())),Z)
 def J(P):return R([Z]+[a/(i+1) for i,a in enumerate(P.coeffs())])
 r=X-ga;ix=[(i,j) for i in range(5) for j in range(i)];A=[]
 def add(f,v,ref):
  A.append([f[i]*v[j] for i,j in ix]+[ref-ga*sum((q*t for q,t in zip(f,v)),Z)])
 for i in range(5):
  e=[O if k==i else Z for k in range(5)]
  add(e,[r(x) for x in xs],J(r)(xs[i]))
  add([b*r(x) for x,b in zip(xs,bs)],e,bs[i]*(I(r)-J(r)(xs[i])))
 for i,j in ((i,j) for i in range(1,6) for j in range(1,7-i)):
  add([b*r(x)**i for x,b in zip(xs,bs)],[r(x)**j for x in xs],I(r**i*J(r**j)))
 return fail(F,A,len(ix))
for p in (19,23,2281):
 assert all(p%d for d in range(2,isqrt(p)+1))
 counts=[0,0,0]
 F=fq_default_ctx(p,lcm(*(f.degree() for f,m in nmod_poly([-1,-2,1],p).factor()[1])),'u')
 R=fq_default_poly_ctx(F);X=R.gen();O=F.one();Z=F.zero()
 roots=[x for x,e in (X*X-2*X-1).roots()]
 I=lambda P:sum((a/(i+1) for i,a in enumerate(P.coeffs())),Z)
 for u,v,ph in product(roots,roots,('SS','SA','AS','AA')):
  a=(1+u)/2;b=(3-u)/2 if ph[0]=='S' else (1+2*u)/2
  c=(1-v)/2;d=(v-1)/2 if ph[1]=='S' else (1-2*v)/2
  xs=[O/2,a,b,c,d];P=R.one()
  for x in xs:P=P*(X-x)
  m=[I(X**j*P) for j in range(3)]
  if m[0]==0:
   if m[1]!=0 or m[2]!=0:continue
   f=None
  else:
   f=m[1]/m[0]
   if m[2]!=f*m[1]:continue
  if f is None:
   counts[0]+=1
   continue
  assert f not in xs and all(x!=y for x,y in combinations(xs,2))
  scr=xs+[f]
  ws=[]
  for i,x in enumerate(scr):
   P0=R.one()
   for j,y in enumerate(scr):
    if j!=i:P0=P0*(X-y)/(x-y)
   ws.append(I(P0))
  if ws[4]==0:
   counts[2]+=1
   continue
  xx=[a,b,f,d,c];ww=[ws[scr.index(w)] for w in xx]
  rec=block(F,R,X,xx,ww)
  assert rec[1] is not None and rec[2]!=0
  counts[1]+=1
  print(p,ph,u,v,xx,ww,'block',rec,flush=True)
 assert counts=={19:[4,4,4],23:[1,3,1],2281:[0,2,0]}[p]
 print(p,'free / fixed inconsistent / silent row8',counts)
