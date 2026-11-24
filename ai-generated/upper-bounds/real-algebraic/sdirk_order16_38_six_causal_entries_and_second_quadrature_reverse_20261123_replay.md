# Standalone order-16 strict real SDIRK proof with 38 actual stages

Save the block as `verify38.py` and run `python3 -B verify38.py` with Node.js on PATH. Only standard Python / Node modules are used. The default certifies both isolated algebraic systems, the actual 16+16 banks, all six causal zeros, all 216 grouped physical coefficients, both literal redirects and the common positive diagonal; it enumerates ordinary rooted trees through ten as an extra implementation check. Run `python3 -B verify38.py --full` to independently check the complete merged 38-stage tableau on all rooted trees through sixteen. Add `--tableau` to emit every physical coefficient of A and b as two outward dyadic numerator bounds with denominator 2^160. This output is an enclosure, not the definition of the algebraic coefficients.

The JavaScript portion is compressed only to keep the note compact; `print(jr)` immediately after decompression shows its source, SHA-256 `5dccc145cc5ca39c1ffc25c185e6cef47e2adedf1537225f6ca30a08c7296266`. No external formula file, solver, dataset, or start-box input is needed. Both real root inclusions are recomputed from short ordinary decimal guesses; the high solver's chord iterations merely improve a candidate center before the independent full-box test. See the companion construction note for why exact zeros hold.

```python

"""Exact fixed-grid word flags; standard library only."""
from fractions import Fraction as F
from math import comb
from itertools import combinations
K=2**1536
class T:
 # Dyadic intervals with an optional single directed derivative.
 def __init__(self,v=0,h=None,d=None):
  if h is None:
   if isinstance(v,T): self.l,self.h,self.d=v.l,v.h,v.d;return
   q=F(v)*K;self.l=q.numerator//q.denominator;self.h=-((-q.numerator)//q.denominator)
  else:self.l,self.h=v,h
  self.d=d
 def __repr__(x):return repr(round((x.l+x.h)/(2*K),12))
 def val(x):return T(x.l,x.h)
 def deriv(x):return x.d if x.d is not None else T(0)
 def __neg__(x):return T(-x.h,-x.l,-x.d if x.d is not None else None)
 def __add__(x,y):
  y=T(y);d=(x.d+y.d if y.d is not None and x.d is not None else x.d if x.d is not None else y.d)
  return T(x.l+y.l,x.h+y.h,d)
 __radd__=__add__
 def __sub__(x,y):return x+-T(y)
 def __rsub__(x,y):return -x+y
 def __mul__(x,y):
  y=T(y);v=[a*b for a in (x.l,x.h)for b in(y.l,y.h)]
  d=x.d*y.val() if x.d is not None else None
  if y.d is not None:d=(d if d is not None else T(0))+y.d*x.val()
  return T(min(v)//K,-((-max(v))//K),d)
 __rmul__=__mul__
 def inv(x):
  assert x.l*x.h>0
  v=T(K*K//x.h,-((-K*K)//x.l))
  if x.d is not None:v.d= -x.d*v*v
  return v
 def __truediv__(x,y):return x*T(y).inv()
 def __rtruediv__(x,y):return x.inv()*y
 def __pow__(x,n):return T(1) if n==0 else x*x**(n-1)
 def nz(x):return x.l*x.h>0
def solve(M,z):
 n=len(M);A=[[T(x)for x in row]+[T(w)]for row,w in zip(M,z)];D=T(1)
 for j in range(n):
  i=max(range(j,n),key=lambda i:max(A[i][j].l,-A[i][j].h))
  a=A[i][j]
  if not a.nz():return
  if i!=j:D=-D;A[i],A[j]=A[j],A[i]
  D*=a
  for i in range(j+1,n):
   h=A[i][j]/a
   for k in range(j+1,n+1):A[i][k]-=h*A[j][k]
 t=[T(0)]*n
 for j in range(n-1,-1,-1):t[j]=(A[j][-1]-sum(A[j][k]*t[k]for k in range(j+1,n)))/A[j][j]
 return t,D
from functools import cache
from itertools import combinations
def add(M,z):
 s=solve(M,z)
 if s is None:raise ZeroDivisionError
 return s[0]
def dot(x,y):return sum(a*b for a,b in zip(x,y))
def proofbasis(cols,k):
 ids=[];piv=[];B=[]
 for ic,u in enumerate(cols):
  w=list(u)
  for i,v in zip(piv,B):
   f=w[i];w=[x-f*y for x,y in zip(w,v)]
  candidates=[j for j in range(k) if T(w[j]).nz()]
  if not candidates:continue
  j=max(candidates,key=lambda j:max(w[j].l,-w[j].h)); q=w[j];v=[x/q for x in w]
  ids.append(ic);piv.append(j);B.append(v)
  if len(B)==k:break
 return ids

from math import comb
from itertools import combinations
from functools import cache
from math import factorial
from functools import cache
def polyroots(rr):
 co=[T(1)]
 for z in rr:co=[a-z*b for a,b in zip([T(0)]+co,co+[T(0)])]
 return co
from functools import lru_cache
RANK={2:1,3:2,4:4,5:6,6:9,7:12,8:17,9:23}
TRACE=None
def choose(M,z,lam=None):
 m=len(M);n=len(M[0])
 js=proofbasis([list(v) for v in zip(*M)],m)
 if TRACE is not None:TRACE.append(('tap',tuple(js)))
 assert len(js)==m,('rowrank',m,n,len(js))
 # independent columns; never use absence of a pivot as a proof of equality
 tap=[T(F((j*17+n*7)%19+1,16))for j in range(n)]
 if lam is not None:
  free=[j for j in range(n)if j not in js];assert free;pos,theta=lam;tap[free[pos]]=theta
 pp=add([[x[j] for j in js]for x in M],[v-sum(x[j]*tap[j] for j in range(n) if j not in js)for x,v in zip(M,z)])
 for j,p in zip(js,pp):tap[j]=p
 return tap
KNOB=None
SEED_ONE=False
def multibuild(Y,sites,maxr,knobs=None,probe=0,stagepol=None,partial=False,other_pol=None,tracepur=False):
 if knobs is None:knobs={}
 c=[Y[i]for i in sites];g=c[0]
 A=[[g],[c[1]-g,g]]
 e2=('d',2);P={1:[],2:[e2],3:[e2,('M',e2)]};rel={}
 eta=(dot(A[1],c[:2])-c[1]**2/2)/(g*g/2)
 rel[3]=[{('I',e2):1,e2:(1/eta-1)*g,('M',e2):-1/eta},
         {('d',3):1,('I',e2):F(-2,3),('M',e2):F(-2,3)}]
 def calc():
  N=len(A)
  @lru_cache(None)
  def val(e):
   op,u=e
   if op=='d':
    power=[x**(u-1)for x in c[:N]]
    return [dot(a,power)-x**u/u for a,x in zip(A,c)]
   v=val(u)
   if op=='M':return [x*y for x,y in zip(c,v)]
   return [dot(a,v)for a in A]
  return val
 for i in range(2,len(sites)+1):
  val=calc()
  for k in range(4,maxr+1):
   if i!=RANK[k]:continue
   old=P[k-1]
   ext=[e for e in old if e not in P[k-2]]
   cand=old+[(o,e) for o in ('M','I') for e in ext]+[('d',k)]
   dim=i-1 if (probe==k) else i
   ids=proofbasis([val(e)[:dim]for e in cand],dim)
   if TRACE is not None:TRACE.append(('def',k,tuple(ids)))
   assert len(ids)==dim and ids[:len(old)]==list(range(len(old))),('level pivot',k,i,len(ids),ids[:len(old)])
   bs=[cand[j]for j in ids];H=list(zip(*(val(e)[:dim]for e in bs)))
   P[k]=bs;rel[k]=[]
   for j,e in enumerate(cand):
    if j in ids:continue
    a=add(H,val(e)[:dim]);rel[k].append({e:1,**{t:-v for t,v in zip(bs,a)}})
  if i==len(sites):
   global ST
   ST=(P,rel,val);break
  u=c[i]
  @lru_cache(None)
  def aff(e):
   op,t=e
   if op=='d':
    return [g*u**(t-1)-u**t/t]+[x**(t-1)for x in c[:i]]
   q=aff(t)
   if op=='M':return [u*v for v in q]
   return [g*q[0]]+[g*x+y for x,y in zip(q[1:],val(t))]
  M=[[T(1)]*i];z=[u-g]
  if i==2 and SEED_ONE: # even tuned grid, one-parent exact grade-three seed
   A.append([u-g,T(0),g]);continue
  for k in range(3,maxr+1):
   for jj,re in enumerate(rel.get(k,[])):
    if i==2 and k==3 and jj==1:continue # third AP row automatically obeys commutator identity
    q=[sum(b*zz for b,zz in zip(re.values(),v))for v in zip(*(aff(t)for t in re))]
    M.append(q[1:]);z.append(-q[0])
  if i==RANK.get(probe,-1):
   v=[T(0)]*(len(M)-len(rel[probe]))+[-sum(b*val(t)[i-1]for t,b in re.items())for re in rel[probe]]
   return [row+[z0]for row,z0 in zip(M,v)],z
  if i in [RANK[k]for k in knobs]:
   js=proofbasis(M,i);assert len(js)==i
   M=[M[j]for j in js];z=[z[j]for j in js]
  param=next((v for k,v in knobs.items()if i==RANK[k]-1),None)
  if KNOB and i==KNOB[0]:param=(KNOB[1],KNOB[2])
  if stagepol and i in stagepol:
   pp=P[maxr];br=RANK[maxr];BB=list(zip(*(val(e)[:br] for e in pp)))
   for H in stagepol[i]:
    aa=add(BB,[evH(H,x)for x in c[:br]])
    hh=[sum(w*x for w,x in zip(aa,row))for row in zip(*(aff(e)for e in pp))]
    M.append(hh[1:]);z.append(evH(H,u)-hh[0])
  if other_pol and i in other_pol:
   for de,H in other_pol[i]:
    pp=P[de];br=RANK[de];BB=list(zip(*(val(e)[:br] for e in pp)))
    aa=add(BB,[evH(H,x)for x in c[:br]])
    hh=[sum(w*x for w,x in zip(aa,row))for row in zip(*(aff(e)for e in pp))]
    M.append(hh[1:]);z.append(evH(H,u)-hh[0])
  try:tap=choose(M,z,param)
  except:raise
  A.append(tap+[g])
 val=calc()
 rr=maxr;ph=[ [v**j for v in c] for j in range(rr)]+[val(e) for e in P[rr-1]]
 if not partial:assert len(ph)==len(c) and solve(ph,[T(0)]*len(c)),('dense',rr,len(c))
 cap=RANK[rr];bp=[val(e)for e in P[rr]]
 raw=[]
 for j in range(cap,len(c)):
  w=add([v[:cap]for v in bp],[-v[j]for v in bp])
  row=[T(0)]*len(Y);row[sites[j]]+=1
  for t,h in zip(sites,w):row[t]+=h
  raw.append(row)
 if tracepur:return raw,A,c,[val(e)for e in P[rr-1]]
 return raw,A,c
def deter(M):
 n=len(M);A=[list(row)for row in M];out=T(1)
 for j in range(n-1):
  i=max(range(j,n),key=lambda i:max(A[i][j].l,-A[i][j].h))
  if not A[i][j].nz():raise ZeroDivisionError('det pivot')
  if i!=j:out=-out;A[i],A[j]=A[j],A[i]
  a=A[j][j];out*=a
  for i in range(j+1,n):
   c=A[i][j]/a
   for k in range(j+1,n):A[i][k]-=c*A[j][k]
 return out*A[-1][-1]
def leib(M):
 n=len(M);v={0:T(1)}
 for row in M:
  w={}
  for b,x in v.items():
   for i in range(n):
    if (b>>i)&1:continue
    y=x*row[i];bb=b|(1<<i)
    w[bb]=w.get(bb,T(0))+(-y if (b>>(i+1)).bit_count()%2 else y)
  v=w
 return v[(1<<n)-1]
from math import isqrt
def sqrtT(x):
 assert x.l>0
 z=T(isqrt(K*x.l),isqrt(K*x.h)+1)
 if x.d is not None:z.d=x.d/(2*z.val())
 return z
def multipar(Y,sites,k,old={},idx=0):
 # The common powers of two are independent of the sampled tap.
 def matrix(t):
  return multibuild(Y,sites,k,{**old,k:(idx,T(t))},probe=k)
 matrices=[]
 for val in (-1,0,1):
  M,z=matrix(val);matrices.append([v+[w]for v,w in zip(M,z)])
 nn=len(matrices[0])
 for i in range(nn):
  b=max(max(abs(c.l),abs(c.h)).bit_length() for M in matrices for c in M[i])-K.bit_length()
  sc=T(F(2)**(-b))
  for M in matrices:M[i]=[v*sc for v in M[i]]
 for j in range(nn):
  b=max(max(abs(M[i][j].l),abs(M[i][j].h)).bit_length()for i in range(nn)for M in matrices)-K.bit_length()
  sc=T(F(2)**(-b))
  for M in matrices:
   for i in range(nn):M[i][j]*=sc
 ff=[]
 for M in matrices:
  try:v=deter(M)
  except ZeroDivisionError:v=leib(M)
  ff.append(v)
 c=ff[1];b=(ff[2]-ff[0])/2;a=(ff[2]+ff[0])/2-c;disc=b*b-4*a*c
 if not disc.l>0:return []
 sq=sqrtT(disc);out=[]
 for j,v in enumerate((b+sq,b-sq)):
  if not v.nz():continue
  th=-2*c/v;M,z=matrix(th);nn=len(M)
  ids=proofbasis(M,nn-1)
  if len(ids)==nn-1:out.append((j,th,idx,ids))
 return out
def evH(P,x):return sum(t*x**j for j,t in enumerate(P))
def prim(P,x):return sum(t*x**(j+1)/(j+1) for j,t in enumerate(P))
def kernels(M,n):
 m=len(M);I=list(range(n))
 for js in combinations(I,m):
  A=[[r[j]for j in js]for r in M]
  if solve(A,[T(0)]*m):break
 else:raise ZeroDivisionError
 U=[]
 for j in I:
  if j in js:continue
  v=[T(0)]*n;v[j]=T(1)
  for t,x in zip(js,add(A,[-r[j] for r in M])):v[t]=x
  U.append(v)
 return U
def sign(x):return 1 if x.l>0 else -1 if x.h<0 else 0

def dex(x):return min(abs(x.l),abs(x.h)).bit_length()-K.bit_length()
def jet(row,e):return [dot(row,col)for col in zip(*e)]

def lcoef(k):return [T(F((-1)**i*comb(k,i),factorial(i))) for i in range(k+1)]
def legcoef(k):return [T((-1)**(k-i)*comb(k,i)*comb(k+i,i)) for i in range(k+1)]
def hor(co,x):
 out=co[-1]
 for v in co[-2::-1]:out=v+x*out
 return out
def det3a(a,b,c):return dot(a,[b[1]*c[2]-b[2]*c[1],b[2]*c[0]-b[0]*c[2],b[0]*c[1]-b[1]*c[0]])
def lowmat(c,defs,r):
 b=len(defs);jet=[]
 for j in range(b,len(c)):
  a=add([v[:b]for v in defs],[-v[j]for v in defs])
  jet.append([c[j]**d+sum(v*x**d for v,x in zip(a,c[:b]))for d in range(r)])
 return jet
# Pure-Python two-parameter bridge at p16. All index lists are zero-based.
def mv(A,x):return [dot(row,x)for row in A]
def mm(A,B):return [mv(list(zip(*B)),row)for row in A]
def cols(A,*vecs):return [list(z)+[v[i]for v in vecs]for i,z in enumerate(A)]
def vsub(a,b):return [x-y for x,y in zip(a,b)]
def axsub(a,s,b):return [x-s*y for x,y in zip(a,b)]
def mtake(A,js):return [[row[j]for j in js]for row in A]
def fsolve(M,z,js,default):
 # The indices are fixed explicitly after one characteristic-zero point test.
 x=list(default);free=[j for j in range(len(x))if j not in js]
 zz=[b-sum(row[j]*x[j]for j in free)for row,b in zip(M,z)]
 pp=add(mtake(M,js),zz)
 for j,p in zip(js,pp):x[j]=p
 return x
def vec(d,n):return [T(d)]*n
import sys,json
PACKAGE=None
def inraw(p):
 return T((int(p[0])*K)//(2**2048),-((-int(p[1])*K)//(2**2048)))
def affine_setup(kn=T(F(3,16)),lam=False):
 global KNOB,SEED_ONE
 KNOB=(11,0,kn)
 SEED_ONE=False;RANK[7]=13
 q=r=7;n=9;Y=YD;seed=[1,4,7]
 Y=[T(u)for u in Y]
 if lam:
  cp=legcoef(9);cpp=[j*x for j,x in enumerate(cp)if j]
  for u in Y:u.d=-hor(legcoef(7),u.val())/hor(cpp,u.val())
 g=Y[1];Y[4]=T(F(1,2));Y[7]=1-g
 w=add([[y**j for y in Y]for j in range(n)],[T(F(1,j+1))for j in range(n)]);assert all(x.l>0 for x in w)
 S=(1,4,7,6,0,5,3,8,6,2,3,0,4,5,8,0);fstars=[6,5];y=Y[S[-1]]
 EL=(7,8); BM=(1,4,2); RU=(3,); skip=(0,*EL,BM[0])
 er=[[u**k for k in range(8)] for u in Y]
 Dh=polyroots([1-Y[j] for j in range(n) if j not in skip])
 Hs=[[T(0)]*k+Dh for k in range(3)]
 cap=kernels([er[j] for j in (0,*EL)],8);assert len(cap)==5
 GG=[[sum(wi*evH(H,1-z)*(prim(p,z)-g*evH(p,z))for z,wi in zip(Y,w))for p in cap]for H in Hs]
 ch=multipar(Y,S[:7],5)[0];kn={5:(ch[2],ch[1])}
 raw,old,c=multibuild(Y,S[:12],6,kn,partial=True)
 ps,rel,val=ST;pl=ps[6];ext=[e for e in pl if e not in ps[5]]
 cand=pl+[(o,e)for o in ('M','I')for e in ext]+[('d',7)]
 ex=[];ix={}
 def gather(e):
  if isinstance(e[1],tuple):gather(e[1])
  if e not in ix:ix[e]=len(ex);ex.append(e)
 for e in cand:gather(e)
 for k in sorted(rel):
  for z in rel[k]:
   for e in z:gather(e)
 E=len(ex);LW=[[d.get(e,T(0))for e in ex]for k in sorted(rel)for d in rel[k]]
 inds=proofbasis([val(e)for e in cand],12);assert len(inds)==12
 J=[cand[j]for j in inds];DX=list(zip(*(val(e)for e in J)));NN=[]
 for j,e in enumerate(cand):
  if j in inds:continue
  v=add(DX,val(e));ff=vec(0,E);ff[ix[e]]=T(1)
  for z,b in zip(v,J):ff[ix[b]]-=z
  NN.append(ff)
 assert len(NN)==4
 prelow=lowmat(c,[val(e)for e in pl],r);lc=kernels(prelow,r);assert len(lc)==4
 mu=[prim(p,y)-g*evH(p,y)for p in lc];eY=[evH(p,y)for p in lc]
 def transform(cap,expr):
  bb=len(expr);M=list(zip(*(val(e)[:bb]for e in expr)));H=[]
  for p in cap:
   xx=add(M,[evH(p,u)for u in c[:bb]]);row=vec(0,E)
   for e,z in zip(expr,xx):row[ix[e]]=z
   H.append(row)
  return H,[[evH(p,Y[j])for p in cap]for j in S[12:]]
 TM,ty=transform(cap,J);KM,ky=transform(lc,pl);base={};dyn={}
 for i in range(12,15):
  u=Y[S[i]]
  @lru_cache(None)
  def aff(e):
   op,b=e
   if op=='d':return [g*u**(b-1)-u**b/b]+[x**(b-1)for x in c]
   v=aff(b)
   if op=='M':return [u*x for x in v]
   return [g*v[0]]+[g*x+y for x,y in zip(v[1:],val(b))]
  D=[aff(e)for e in ex];base[i]=[D]+[mm(U,D)for U in (LW,NN,TM,KM)]
  for j in range(12,i):
   cj=Y[S[j]]
   @lru_cache(None)
   def dcol(e):
    op,b=e
    if op=='d':return [cj**(b-1)]+vec(0,E)
    v=dcol(b)
    if op=='M':return [u*x for x in v]
    h=[g*x for x in v];h[1+ix[b]]+=1;return h
   dyn[i,j]=[dcol(e)for e in ex]
 env=locals(); return {v:env[v] for v in "BM EL GG KM LW NN RU S TM Y base cap dyn eY fstars g ix ky mu n old pl r ty val w y".split()}

def rnd(x):return T(F(str(x)))
def cen(x):v=(x.l+x.h)//2;return T(v,v)
def l1(x):return max(abs(x.l),abs(x.h))
def halfsgn(x):return -1 if x.h<0 else 1 if x.l>0 else 0
def interroot(lam):
 pp=legcoef(9);qq=legcoef(7)
 cc=[u+(lam.val()*qq[j] if j<8 else 0)for j,u in enumerate(pp)];dp=[j*x for j,x in enumerate(cc) if j];roots=[]
 for x0 in ('.016515878','.084538688','.197383179','.341091675'):
  x=rnd(x0);md=list(map(cen,cc));dd=list(map(cen,dp))
  for _ in range(12):x=cen(x-hor(md,x)/hor(dd,x))
  err=l1(hor(cc,x)/hor(dp,x));delta=max(12,3*err);x=T(x.l-delta,x.h+delta)
  assert sign(hor(cc,T(x.l,x.l)))*sign(hor(cc,T(x.h,x.h)))==-1 and hor(dp,x).nz()
  if lam.d is not None:x.d=-lam.d*hor(qq,x.val())/hor(dp,x.val())
  roots.append(x)
 return roots+[T(F(1,2))]+[1-x for x in roots[::-1]]
def mlag(P):
 return [sum(P[j]*factorial(j)*comb(j,k)*(-1)**k for j in range(k,len(P)))for k in range(len(P))]
def dl(P):return [j*x for j,x in enumerate(P) if j]
def ep(P,j):return [T(0)]*j+P
def proot(roots):return polyroots(roots)
def cvrow(x,n):return [hor(lcoef(i),x)for i in range(n)]
def kk2(B,Tn,x):
 z=[Tn(p,x)for p in B];ii=max(range(len(z)),key=lambda j:l1(z[j]));assert z[ii].nz()
 BB=[r+vec(0,7-len(r))for r in B];return [axsub(v,z[j]/z[ii],BB[ii]) for j,v in enumerate(BB)if j!=ii]
def geom(X,Y,W,EL,BM,R):
 s,t,z,u=X[:4];g=Y[1];v=(1-Y[6])/g;w=(1-Y[5])/g;Muv=lambda P,x:prim(P,x)-evH(P,x)
 p=proot([T(0),s,s,t,t]);b=[dl(ep(p,i)) for i in range(3)];q=proot([s,t,z,u]);e=[ep(q,i)for i in range(3)]
 U=list(map(mlag,kk2(b,Muv,z)+kk2(e,Muv,v)));F6=vec(0,2)+add([r[2:6]for r in U],[-r[6]for r in U])+[T(1)]
 def mix(x,lo,prev):
  E=[cvrow(j,7) for j in prev];mu=[[-v for v in cvrow(j,8)[1:]]for j in prev];M=([F6]if lo else [])+E+mu;n=len(M)
  h=add([list(p)for p in list(zip(*M))[:n]],[-v for v in cvrow(x,8)[1:n+1]])[-len(prev):];return [zz-sum(y*xx for y,xx in zip(h,pp))for zz,pp in zip(cvrow(x,8),zip(*(cvrow(j,8)for j in prev)))]
 raw=[mix(z,True,[s,t]),mix(u,False,[s,t,z])]
 D3=proot([T(0),s,s,t,t,z,z]);P5=proot([s,t,z,u,v]);bb=prim(ep(P5,1),v)/prim(P5,v);FQ=proot([s,t,z,u,v,bb]);ge=[evH(D3,u)-evH(dl(D3),u),Muv(FQ,w)]
 def bs(Z,n):return [ep(proot(Z),j)for j in range(n-len(Z))]
 upper=bs([1-Y[j]for j in [6,5,R]],8)
 def obs(h,p):return dot(h,mlag([a*g**j for j,a in enumerate(p)]))
 def gr(h,k):return sum(a*evH(h,1-y)*(prim(k,y)-g*evH(k,y))for a,y in zip(W,Y))
 Mat=[[obs(f,h) for h in upper] for f in raw]+[[evH(h,1-Y[j])for h in upper] for j in BM];Hc=[list(map(lambda rr:dot(add(Mat,vec(0,2)+[T(j==i)for j in range(3)]),rr),zip(*[h+vec(0,8-len(h))for h in upper])))for i in range(3)]
 KS=[];Kq=None
 for i,jj in enumerate(BM):
  kk=bs([Y[t]for t in (0,*EL,*[u for u in BM if u!=jj])],8);ra=[[evH(k,Y[jj])for k in kk]]+[[gr(H,k)for k in kk]for H in Hc[:min(2,i+1)]]
  def pc(co):return [dot(rr,co) for rr in zip(*[p+vec(0,8-len(p)) for p in kk])]
  if i==0:
   q=add([r[:2]for r in ra],[T(1),T(0)])+[T(0)];Kq=pc(add([r[:2]for r in ra],[-r[2]for r in ra])+[T(1)])[3:]
  else:q=add(ra,[T(1),T(0),T(0)])
  k=pc(q);KS.append(k[3:])
  if i==2:ge.append(gr(Hc[2],k))
 return ge,KS,Kq,Hc,raw,F6
def frame(k,lam):
 global YD
 YD=interroot(lam);return affine_setup(k)
def coeff(fr,abc,sites,detail=False):
 D0=[fr[k] for k in ('base','dyn','LW','NN','TM','KM','ty','ky','mu','Y','g','S','EL','BM','RU','old','pl','val')];base,dyn,LW,NN,TM,KM,ty,ky,mu,Y,g,S,EL,BM,RU,old,pl,val=D0
 ge,KS,Kq,Hc,raw,F6=sites;xv=[];taps=[];wlow=[];au,bu=abc;
 for off,i in enumerate(range(12,15)):
  dc=[mv(dyn[i,j],[T(1),*xv[j-12]])for j in range(12,i)]
  if dc:
   cr=list(zip(*dc));more=[cr]+[mm(U,cr) for U in (LW,NN,TM,KM)];D,lo,up,Tr,Kr=[[list(row)+list(co)for row,co in zip(bg,cg)]for bg,cg in zip(base[i],more)]
  else:D,lo,up,Tr,Kr=base[i]
  LM=[[g-Y[S[i]]]+vec(1,i)]+lo
  if off==0:
   tx=fsolve([r[1:]for r in LM],[-r[0]for r in LM],list(range(9)),vec(0,9)+[T(1),au,bu]);ev=[T(1)]+tx
   rv=mv(up,ev);wt0=vsub(ty[off],mv(Tr,ev));assert any(z.nz()for z in rv)
  else:
   MM=LM+[[row[0]-q,*row[1:]]for row,q in zip(up,rv)]
   if off==2:
    hu=mv(list(zip(*Tr)),KS[2]);hu[0]-=dot(ty[off],KS[2])-dot(wt0,KS[2]);MM.append(hu)
   tx=add([r[1:]for r in MM],[-r[0]for r in MM]);ev=[T(1)]+tx
   w=vsub(vsub(ty[off],mv(Tr,ev)),wt0)
   if off==1:w1=w
   else:w2=w
  wlow.append(vsub(ky[off],mv(Kr,ev)));taps.append(tx);xv.append(mv(D,ev))
 K1=axsub(KS[0],dot(w1,KS[0])/dot(w1,Kq),Kq)
 out=ge+[dot(w1,KS[1]),dot(w1,KS[2]),dot(w2,KS[1]),dot(w2,K1),leib(wlow+[mu])]
 if detail:return out,dict(taps=taps,xv=xv,wlow=wlow,w1=w1,w2=w2)
 return out
def mechanism(X,fr=None):
 if fr is None:fr=frame(X[4],X[5])
 g=geom(X,fr['Y'],fr['w'],(7,8),(1,4,2),3)
 return coeff(fr,X[6:8],g)
def makeX(x,b=None):
 return [T(v.l,v.h,T(1) if b==i else None)for i,v in enumerate(x)]
def jac8(x,cached=None):
 fc=frame(x[4],x[5])if cached is None else cached
 rows=[]
 for i in range(8):
  X=makeX(x,i);rr=mechanism(X,None if i in (4,5)else fc);rows.append([p.deriv()for p in rr])
 return [list(v)for v in zip(*rows)]
def pfloat(x):return (x.l+x.h)/(2*K)
xx=list(map(rnd,["7.6519502428","4.6837188386","2.6024199560","12.1763719953","-0.3009733947","-0.0229704514","0.2324027750","-0.5358703110"]))
from time import time
start=time()
for outer,count in enumerate((6,13)):
 fr=frame(xx[4],xx[5]);J=jac8(xx,fr);PJ=[[cen(z)for z in row]for row in J]
 for ny in range(count):
  d=add(PJ,mechanism(xx,fr if ny==0 else None));xx=[cen(v-z)for v,z in zip(xx,d)]
  if ny==0 or ny==count-1:print('center correction',outer,ny,max(l1(z).bit_length()-K.bit_length() for z in d),round(time()-start),flush=True)
rad=K>>620;box=[T(x.l-rad,x.h+rad)for x in xx];fc=frame(xx[4],xx[5]);fb=frame(box[4],box[5]);J=jac8(box,fb)
M=list(zip(*(add(PJ,[T(i==j)for i in range(8)])for j in range(8))));M=[[cen(v)for v in row]for row in M]
dotmat=lambda A,B:[[dot(row,col)for col in zip(*B)]for row in A]
U=dotmat(M,J);lip=max(sum(l1(T(i==j)-z) for j,z in enumerate(row))for i,row in enumerate(U));off=max(l1(z)for z in mv(M,mechanism(xx,fc)))
print('exact directed joint',dex(deter(J)),lip.bit_length()-K.bit_length(),off.bit_length()-K.bit_length(),round(time()-start),flush=True)
assert lip<K and off*K+lip*rad<rad*K
print('isolated high center',list(map(pfloat,xx)),flush=True)

def verify_bank(XX,fb,canon=False):
 S,Y,ww,g,bm,el,rr,pl,val,idx,pold=[fb[k]for k in ('S','Y','w','g','BM','EL','RU','pl','val','ix','old')]
 cc=[Y[j]for j in S];ge=geom(XX,Y,ww,el,bm,rr[0]);w8,dd=coeff(fb,XX[6:],ge,True);assert all(t.l<=0<=t.h for t in w8)
 assert leib([fb['eY']]+dd['wlow']).nz(), "old terminal evaluation separates the lower flag"
 assert Y[0].l>0 and Y[-1].h<K and all(Y[j].h<Y[j+1].l for j in range(8))
 for j in range(16):assert not (sum(ww0*y**j for ww0,y in zip(ww,Y))-T(F(1,j+1))).nz()
 A=pold+[tx+[g]for tx in dd['taps']];fields=[val(e)+[row[idx[e]]for row in dd['xv']] for e in pl];lower=[[u**d for u in cc[:15]]for d in range(7)]+fields;tgt=[cc[-1]**(d+1)/(d+1)-g*cc[-1]**d for d in range(7)]+vec(0,len(fields));ids=proofbasis(lower,15);assert len(ids)==15;theta=add([lower[j]for j in ids],[tgt[j]for j in ids]);oldgrp=[i for i in range(15)if S[i]==0];xx=[(1+len(oldgrp))*z for z in theta]
 for i in oldgrp:
  for j in range(i):xx[j]-=A[i][j]
 A.append(xx+[g]);grp=oldgrp+[15];cleanend=[T(F(1,len(grp)))if j in grp else T(0)for j in range(16)];layer=[(vec(1,16),T(1))];words=[];pure=[];tags=[]
 for d in range(8):
  for vv,cf in layer:
   p=[v-cf*x**d for v,x in zip(vv,cc)];pure.append(p);words.append(vv);tags.append((d,cf));er=dot(cleanend,p);assert er.l<=0<=er.h
  layer=[(vw,cw)for v,cf in layer for vw,cw in [([u*z for u,z in zip(cc,v)],cf),([dot(row,v)for row in A],cf/(d+1))]]
 assert len(words)==255 and len(proofbasis(words[:127],16))==16
 ii=proofbasis([p[:13]for p in pure],13);assert len(ii)==13;PM=[pure[j][:13]for j in ii];oldhi=[add(PM,[-pure[j][i]for j in ii])+[T(j==i)for j in range(13,16)]for i in [13,14]]+[cleanend]
 for h in oldhi:
  for v in pure:
   e=dot(h,v);assert e.l<=0<=e.h
 sr=[[dot(h,[u**j for u in cc])for j in range(8)]for h in oldhi];ev=[[y**j for j in range(8)] for y in Y];VV=sr+[ev[i]for i in (*el,*bm)];AA=deter(VV);bsm=ge[3];card=[add(VV,vec(0,5)+[T(i==j)for j in range(3)])for i in range(3)];errs=[]
 for i,H in enumerate(bsm):
  for j in range(i,3):errs.append(sum(W*evH(H,1-u)*(prim(card[j],u)-g*evH(card[j],u))for W,u in zip(ww,Y)))
 assert all(v.l<=0<=v.h for v in errs)
 il=proofbasis(pure[:127],16);assert len(il)==9;ft=[[u**j for u in cc]for j in range(7)]+[pure[i]for i in il];Dc=deter(ft)
 ps=[];tt=list(zip(*ft))
 for ii in range(127,255):
  v=add(tt,words[ii])[:7];ps.append([-q for q in v]+[tags[ii][1]])
 jh=proofbasis(ps,8);assert len(jh)==5;cols0=proofbasis(list(zip(*[ps[j]for j in jh])),5);dl=deter(mtake([ps[j]for j in jh],cols0));weights=[ww[j]/(S.count(j)+(j!=0))for j in range(9)];assert min(v.l for v in weights)>0
 print('all 255, dense, high, reverse cardinal, omitted entries, shares',dex(Dc),dex(dl),dex(AA),max(l1(z).bit_length()-K.bit_length()for z in errs),min(dex(z)for z in weights),flush=True)
 return A,cc,sr,ge,ft,weights

def physical_reverse(XX,fb,output):
 A,c,Sr,GG,FT,sw=output;Y,W,g,sites=fb['Y'],fb['w'],fb['g'],fb['S'];el=(7,8);bm=(1,4,2);rr=(3,);prot=(6,5);ordr=(*el,*bm,*rr,*prot);N=16+8
 ev=[[u**j for j in range(8)]for u in Y];ex=[[(1-u)**j for j in range(8)]for u in Y]
 f=[[g**j*factorial(j)*sum((-1)**k*comb(j,k)*h[k]for k in range(j+1))for j in range(8)]for h in GG[4]]
 Fmat=f+[ex[j]for j in prot]+[ex[j]for j in (*bm,*rr)];Vmat=Sr+[ev[j]for j in (*el,*bm)]
 H=[add(Fmat,vec(0,4)+[T(i==j)for j in range(4)])for i in range(4)];V=[add(Vmat,vec(0,3)+[T(i==j)for j in range(5)])for i in range(5)]
 def gram(h,k):return sum(w*evH(h,1-u)*(prim(k,u)-g*evH(k,u))for w,u in zip(W,Y))
 pos={j:i for i,j in enumerate(ordr)};S=[vec(0,9)for i in range(9)]
 for i in range(9):S[i][i]=g
 for h,i in zip(H,(*bm,*rr)):
  for k,j in zip(V,(*el,*bm)):
   gv=gram(h,k)
   if pos[j]<pos[i]:S[i][j]=gv/W[i]
   else:assert not gv.nz()
 ico=list(zip(*[add(list(zip(*FT)),[T(i==j)for j in range(16)])[:7]for i in range(16)]))
 phy=list(sites)+list(ordr);D=[[T(F(1,phy.count(j)))if lab==j else T(0)for lab in phy]for j in range(9)]
 E=[];J=[]
 for y in Y:
  E.append([dot([y**t for t in range(7)],row)for row in zip(*ico)]+vec(0,8))
  J.append([dot([y**(t+1)/(t+1)for t in range(7)],row)for row in zip(*ico)]+vec(0,8))
 L=[row+vec(0,N-len(row))for row in A]
 for i in ordr:
  ri=len(L);row=axsub(J[i],g,E[i]);m=phy.count(i)
  for j in range(9):
   if j!=i:row=[a+S[i][j]*(b-e)for a,b,e in zip(row,D[j],E[j])]
  row=[z*m for z in row]
  for j in range(16):
   if sites[j]==i:
    for h in range(j):row[h]-=L[j][h]
  assert all(not v.nz()for v in row[ri:]);row[ri:]=[g]+vec(0,N-ri-1);L.append(row)
 act=mm(D,L);model=mm(S,[vsub(d,e)for d,e in zip(D,E)]);eb=[]
 for ar,mod,jv in zip(act,model,J):
  for val,sm,z in zip(ar,mod,jv):
   v=val-sm-z;assert not v.nz();eb.append(l1(v))
 for posn in (N-2,N-1):
  assert all(L[j][posn].l==L[j][posn].h==0 for j in range(posn+1,N)) and L[posn][posn].nz()
 print('24 reverse rows, 216 grouping coefficients, forward cardinal separation',max(eb).bit_length()-K.bit_length(),dex(deter(Fmat)),flush=True)
 return L,phy,H,V

old=verify_bank(box,fb);mm=physical_reverse(box,fb,old);print('ROOTPROFILES',','.join(str(pfloat(v))for v in box),'g=',pfloat(fb['g']),flush=True)

import subprocess,sys,json,zlib,base64
def iv(x):return [str(x.l),str(x.h)]
data={'X':list(map(iv,box)),'W':list(map(iv,fb['w'])),'Y':list(map(iv,fb['Y'])),'raw':[list(map(iv,r))for r in old[3][4]],'L':[list(map(iv,r))for r in mm[0]],'phy':mm[1]}
jr=zlib.decompress(base64.b64decode('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')).decode();import hashlib;assert hashlib.sha256(jr.encode()).hexdigest()=='5dccc145cc5ca39c1ffc25c185e6cef47e2adedf1537225f6ca30a08c7296266'
cp=subprocess.run(['node','-e',jr,'--',*[v for v in sys.argv[1:] if v in ('--full','--tableau')]],input=json.dumps(data),text=True,check=True)

```
