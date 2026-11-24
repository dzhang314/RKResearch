from fractions import Fraction as Q
from math import gcd
from functools import reduce
from itertools import combinations
from time import time
import sympy as S
# Q(t,v), v^2=7, 63t^4-84t^2+16=0, t=A+B on the chosen positive Lobatto branch.
n=8; B=63**2
from collections import defaultdict
def prod(i,j):
 a=(i%4)+(j%4);z=(i//4)+(j//4);b=7 if z==2 else 1;z%=2
 def red(a):
  if a<4:return {a:Q(1)}
  k=defaultdict(Q)
  for s,g in ((a-2,Q(4,3)),(a-4,Q(-16,63))):
   for degree,c in red(s).items():k[degree]+=g*c
  return k
 return [(i+4*z,int(u*b*B)) for i,u in red(a).items()]
MT=[[prod(i,j) for j in range(n)]for i in range(n)]
class F:
 __slots__=('r','d')
 @classmethod
 def raw(cls,nums,den):
  z=object.__new__(cls);g=reduce(gcd,nums,den)
  if den<0:g=-abs(g)
  z.r=tuple(k//g for k in nums) if g!=1 else tuple(nums);z.d=den//g
  return z
 def __new__(c,x=0):
  if isinstance(x,c):return x
  z=Q(x);return c.raw((z.numerator,)+(0,)*7,z.denominator)
 def __eq__(s,t):
  t=F(t);return s.d==t.d and s.r==t.r
 def __bool__(s):return any(s.r)
 def __neg__(s):return F.raw([-a for a in s.r],s.d)
 def __add__(s,t):
  t=F(t)
  if not s:return t
  if not t:return s
  g=gcd(s.d,t.d);a=t.d//g;b=s.d//g
  return F.raw([a*x+b*y for x,y in zip(s.r,t.r)],s.d*a)
 __radd__=__add__
 def __sub__(s,t):return s+-F(t)
 def __rsub__(s,t):return F(t)+ -s
 def __mul__(s,t):
  t=F(t)
  if not s or not t:return Z
  if not any(t.r[1:]):return F.raw([c*t.r[0] for c in s.r],s.d*t.d)
  if not any(s.r[1:]):return t*s
  a=[0]*n
  for i,x in enumerate(s.r):
   if x:
    for j,y in enumerate(t.r):
     if y:
      xy=x*y
      for k,m in MT[i][j]:a[k]+=m*xy
  return F.raw(a,s.d*t.d*B)
 __rmul__=__mul__
 def __truediv__(s,t):return s*inv(F(t))
 def __rtruediv__(s,t):return F(t)/s
 def __pow__(s,k):return F(1) if k==0 else (s*s)**(k//2)*(s if k%2 else 1)
Z=F(0);O=F(1)
def basis(i):return F.raw([int(j==i) for j in range(n)],1)
from functools import lru_cache
@lru_cache(maxsize=None)
def inv0(r,d):
 s=F.raw(r,d);cols=[s*basis(i) for i in range(n)]
 M=S.Matrix([[S.Rational(c.r[j],c.d) for c in cols] for j in range(n)])
 x=M.inv()[:,0];u=reduce(S.ilcm,[v.q for v in x],1);return F.raw([int(u*v) for v in x],int(u))
def inv(s):
 if not any(s.r[1:]):return F(Q(s.d,s.r[0]))
 return inv0(s.r,s.d)
def solve(R,v):
 a=[list(r)+[w] for r,w in zip(zip(*R),v)]
 for k in range(len(a)):
  j=next(j for j in range(k,len(a)) if a[j][k]);a[k],a[j]=a[j],a[k]
  w=inv(a[k][k]);a[k][k:]=[x*w for x in a[k][k:]]
  for j in range(len(a)):
   if k!=j and a[j][k]:
    w=a[j][k];a[j][k:]=[u-w*x for u,x in zip(a[j][k:],a[k][k:])]
 return [r[-1] for r in a]
def e(t,q):return [t**j for j in range(q)]
def it(t,q,h=0):return [t**(j+1+h)/(j+1+h) for j in range(q)]
def dot(a,b):return sum((v*w for v,w in zip(a,b) if v and w),Z)
def lin(co,rows):return [dot(co,c) for c in zip(*rows)]
def col(i,s):return [F(int(i==j)) for j in range(s)]
def span(P,U,v):return lin(solve(P,v),U)
def append(R,row):
 assert len(row)==len(R)+1
 for r in R:r.append(Z)
 R.append(row)
def padded(r,n):return r+[Z]*(n-len(r))
def disk(p):
 m=4 if p<10 else 5
 if m==4:
  G=[[0],[Q(1,4),Q(1,4)],[0,1,0]];b=[Q(1,6),Q(2,3),Q(1,6)]
 else:
  G=[[0],[Q(1,6),Q(1,6)],[Q(1,6),Q(1,3),Q(1,6)],[Q(1,4),0,0,Q(1,4)],[0,Q(27,22),Q(27,22),Q(-16,11),0]]
  b=[Q(11,120),Q(27,40),Q(27,40),Q(-8,15),Q(11,120)]
 return m,G,b
def forward(p,a,v):
 m,G,b=disk(p);s=len(G);n=s+2;w=[F(u)*a for u in b]
 G=[padded([F(u)*a for u in row],s) for row in G];c=[sum(r,Z) for r in G]
 append(G,w+[Z]);Pc=[e(Z,m),e(a,m)]+[it(a,m,h) for h in range(m-3)]+[e(v,m)]
 U=[col(0,n),col(s,n)]+[padded([x*z**h for x,z in zip(w,c)],n) for h in range(m-3)]+[col(s+1,n)]
 row=span(Pc,U,it(v,m));append(G,row)
 assert span(Pc,U,it(a,m))==G[s] and span(Pc,U,e(v,m))==col(n-1,n)
 return G,(Pc,U),lambda y:span(Pc,U,it(y,m)),lambda y:span(Pc,U,e(y,m)),[s,s+1]
def reflect(p,grid):
 j=3 if p==8 else 4
 if j==3:
  a,b=grid[1],grid[2];t=[Z,a,b];R=[padded([Z],3),[a/2,a/2,Z]]
  P=[e(v,3) for v in t];U=[col(i,3) for i in range(3)];R.append(span(P,U,it(b,3)))
  return t,R,(lambda y:span(P,U,it(y,3))),[2]
 a,b,d,c=[grid[k] for k in (5,1,2,3)];t=[Z,a,b,d,c];n=len(t)
 R=[padded([Z],n),padded([a/2,a/2],n)]
 coeff=solve([e(v,4) for v in (Z,b,a,d)],it(d,4));h=coeff[2]/coeff[1]
 p3=[e(v,3) for v in (Z,a,b)];u3=[col(i,n) for i in range(3)]
 Ib=span(p3,u3,[z+h*y for z,y in zip(it(b,3),it(a,3))]);R.append([z-h*y for z,y in zip(Ib,R[1])])
 B=[z+h*y for z,y in zip(e(b,4),e(a,4))]
 Bub=[z+h*y for z,y in zip(col(2,n),col(1,n))]
 P=[e(Z,4),B,e(d,4),e(c,4)];U=[col(0,n),Bub,col(3,n),col(4,n)]
 R.append(lin([coeff[0],coeff[1],coeff[3]],[U[0],U[1],U[2]]));R.append(span(P,U,it(c,4)))
 assert R[3]==span(P,U,it(d,4))
 return t,R,lambda y:span(P,U,it(y,4)),[2,3]
def gridfor(p):
 t=basis(1);v=basis(4)
 if p==8:
  a=(21*(t*t-Q(2,3))/2)/7
  return [Z,(O-a)/2,O/2,(O+a)/2,O]
 delta=4*v/(21*t);a=(t+delta)/2;b=(t-delta)/2
 assert 21*a**4-14*a**2+1==0 and 21*b**4-14*b**2+1==0
 return [Z,(O-a)/2,(O-b)/2,(O+b)/2,(O+a)/2,O]
def full(p):
 g=gridfor(p);m=len(g);weights=solve([e(t,m) for t in g],it(O,m))
 assert all(weights) and all(dot(weights,[t**j for t in g])==F(1)/(j+1) for j in range(p))
 y,R,br,singles=reflect(p,g);ri=len(y)
 ordinary=[j for j in range(1,m-1) if j not in singles];fy=list(reversed(ordinary));assert len(fy)==2
 G,_,bp,ep,ach=forward(p,O-g[fy[0]],O-g[fy[1]]);nf=len(G)
 idx=[g.index(v) for v in y]
 reps=ordinary+[m-1];idx+=reps
 w=[weights[j]/idx.count(j) for j in idx];nr=len(w)
 L=[padded(r,nr) for r in R]
 for i,j in enumerate(reps,ri):
  row=br(g[j]);sw=[dot([w[l] for l in range(ri) if idx[l]==j],[R[l][k] for l in range(ri) if idx[l]==j]) for k in range(ri)]
  L.append(padded([(weights[j]*x-s)/w[i] for x,s in zip(row,sw)],nr))
 assert all(sum(row,Z)==g[j] for row,j in zip(L,idx))
 Tr=[[w[j]*L[j][i]/w[i] for j in reversed(range(nr))] for i in reversed(range(nr))]
 w=w[::-1];ix=idx[::-1];xx=[O-g[j] for j in ix]
 D=[ep(t) for t in xx]
 A=[padded(r,nf+nr) for r in G]
 for t,row in zip(xx,Tr):
  scl=lin(row,D);A.append([x-v for x,v in zip(bp(t),scl)]+row)
 b=[Z]*nf+w
 merg={nf+l:(0 if j==m-1 else ach[fy.index(j)]) for l,j in enumerate(ix[:len(reps)])}
 for i,tar in merg.items():
  assert A[i]==A[tar]
  for rr in A:rr[tar]+=rr[i]
  b[tar]+=b[i]
 keep=[j for j in range(len(b)) if j not in merg]
 A=[[A[i][j] for j in keep] for i in keep];b=[b[i]for i in keep]
 assert len(b)=={8:8,9:10,10:12}[p] and not any(A[0]) and not any(a for i,row in enumerate(A) for a in row[i+1:])
 return A,b
def alltree(p):
 A,b=full(p);s=len(b);vec=[];av=[];size=[];facts=[];counts=[];start=time()
 for m in range(1,p+1):
  beg=len(vec)
  def gen(n,k):
   if n==0:yield ();return
   for i in range(k,beg):
    if size[i]>n:break
    for suff in gen(n-size[i],i):yield (i,)+suff
  for T in gen(m-1,0):
   w=[O]*s;fac=m
   for j in T:w=[z*y for z,y in zip(w,av[j])];fac*=facts[j]
   assert dot(b,w)*fac==1,(m,T)
   size.append(m);facts.append(fac);vec.append(w)
   if m<p:av.append([dot(row,w) for row in A])
  counts.append(len(vec)-beg)
 print(p,len(b),counts,'all exactly zero;',round(time()-start,1),'s',flush=True)

if __name__ == "__main__":
    from pathlib import Path
    import json, sys
    from math import lcm
    alltree(8)
    A,b=full(8)
    def sq21(f):
        assert all(x==0 for i,x in enumerate(f.r) if i not in (0,2))
        c,d=(Q(f.r[j],f.d) for j in (0,2))
        return (c+Q(2,3)*d,Q(2,21)*d)
    rows=[[sq21(a) for a in row] for row in A]
    b8=[sq21(a) for a in b]
    DA=lcm(*(v.denominator for row in rows for a in row for v in a))
    DB=lcm(*(v.denominator for a in b8 for v in a))
    row_sums=[sum(a,Z) for a in A]
    fail=sq21(9*dot(b,[x**8 for x in row_sums])-1)
    print("All coefficients lie in Q(sqrt(21)); denominator factors:",DA,DB)
    print("Nonzero order-nine bush difference:",tuple(str(q) for q in fail))
    assert fail != (0,0)
    payload={
        'normalForm':'a+b*sqrt(21)',
        'stageDen':DA, 'weightDen':DB,
        'A':[[[int(q*DA) for q in pair] for pair in row] for row in rows],
        'b':[[int(q*DB) for q in pair] for pair in b8],
        'ninthBushDifference':[str(q) for q in fail],
    }
    if len(sys.argv)>1:
        Path(sys.argv[1]).write_text(json.dumps(payload,indent=2)+'\n')
