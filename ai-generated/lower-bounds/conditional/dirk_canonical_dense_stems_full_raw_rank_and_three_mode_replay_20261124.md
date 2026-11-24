# Four sharp canonical dense-order returns: same raw pure minor on every split coefficient branch, and the first causal extension obstruction

Companion to `dirk_one_self_tapped_hermite_relay_p16_and_sharp_canonical_dense_stems_20261124.md`. Run these three Python 3 / SymPy blocks consecutively in one script. A prime splitting every donor tower is selected. The first factor chooses a fixed word list and a fixed row-index list at each grade; the same square minor must then have full modular rank on every one of the eight or sixteen simple factors. With a completely split coefficient algebra, this is the claimed characteristic-zero unit test for those actual minors, not a guess from a zero modular determinant. The two inputs are the standard characteristic-zero P8–P12 tableau builders, of which only P8, P9, P10 and P11 are used here. Modular denominators at every compiled coefficient are inverted explicitly.

```python
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


import sympy as sp
def roots1(p,small):
 def rt(a):return list(map(int,sp.sqrt_mod(a %p,p,all_roots=True)))
 if small:a,b,j=4*pow(3,-1,p),16*pow(63,-1,p),7
 else:a,b,j=20*pow(11,-1,p),80*pow(363,-1,p),15
 return [t for w in rt(a*a-4*b) for t in rt((a+w)*pow(2,-1,p))],rt(j)
def find(p0):
 m=p0;AA,bb=full(m);small=m<=10
 for p in map(int,sp.primerange(1000,100000)):
  T,V=roots1(p,small)
  if len(T)!=4 or len(V)!=2:continue
  B=[];OK=True
  for t in T:
   for v in V:
    def res(x):return sum(k*t**(i%4)*v**(i//4) for i,k in enumerate(x.r))*pow(x.d,-1,p)%p
    if small: roots=[0]
    else:
     try:aa,bc=res(KA),res(KB)
     except ValueError:OK=False;break
     dd=(aa*aa-4*bc)%p;roots=[(-aa+int(j))*pow(2,-1,p)%p for j in sp.sqrt_mod(dd,p,all_roots=True)]
     if len(roots)!=2:OK=False;break
    for z in roots:
     rate=lambda h:res(h) if small else (res(h.x)+z*res(h.y))%p
     try:B.append(([[rate(x) for x in r] for r in AA],[rate(x) for x in bb]))
     except ValueError:OK=False;break
   if not OK:break
  if OK:return p,B
 raise ValueError("no prime")
def rk(A,b,p,g,probe=None,rows=None):
 A=[r+[0] for r in A]+[b+[0]];n=len(A);c=[sum(r)%p for r in A]
 def mv(x):return [sum(q*v for q,v in zip(row,x))%p for row in A]
 L={};words=[];I=[]
 if probe is None:ws=[''.join(w) for k in range(g+1) for w in __import__('itertools').product('CA',repeat=k)]
 else:ws=probe
 zc={'':[1]*n}
 def word(s):
  if s not in zc:
   v=word(s[:-1]);zc[s]=[(u*w)%p for u,w in zip(c,v)] if s[-1]=='C' else [len(s)*w%p for w in mv(v)]
  return zc[s]
 for s in ws:
  v=word(s);w=[(a-pow(x,len(s),p))%p for a,x in zip(v,c)]
  if rows is not None:w=[w[i] for i in rows]
  for i,r in L.items():
   if w[i]:w=[(a-w[i]*b)%p for a,b in zip(w,r)]
  j=next((i for i,t in enumerate(w) if t),None)
  if j is not None:
   L[j]=[t*pow(w[j],-1,p)%p for t in w];I.append(j);words.append(s)
 return words,I
def go(m):
 p,B=find(m);q={8:8,9:9,10:9,11:10}[m]
 for g in (q-2,q-1):
  w,r=rk(*B[0],p,g);dim=len(B[0][1])+1-len(w);print(m,q,g,'truth',dim,'prime',p,'branches',len(B),'selected',w,r,flush=True)
  for A,b in B:assert len(rk(A,b,p,g,w,r)[0])==len(r)
  assert dim==2+(m-g)

for m in [8,9,10]:go(m)
```

Second donor family and the P11 test, preserving the functions `go`, `find` and `rk` from the preceding block:

```python
from fractions import Fraction as Q
from math import gcd
from functools import reduce
from itertools import combinations
from time import time
import sympy as S
# Q(t,v), v^2=7, 63t^4-84t^2+16=0, t=A+B on the chosen positive Lobatto branch.
n=8; B=363**2
from collections import defaultdict
def prod(i,j):
 a=(i%4)+(j%4);z=(i//4)+(j//4);b=15 if z==2 else 1;z%=2
 def red(a):
  if a<4:return {a:Q(1)}
  k=defaultdict(Q)
  for s,g in ((a-2,Q(20,11)),(a-4,Q(-80,363))):
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
  if not s or not t:return F(0)
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

binv=inv
KA=F(0);KB=F(0)
class A:
 __slots__=('x','y')
 def __new__(q,x=0,y=0):
  if isinstance(x,A):return x
  z=object.__new__(q);z.x=F(x);z.y=F(y);return z
 def __eq__(a,b):b=A(b);return a.x==b.x and a.y==b.y
 def __bool__(a):return bool(a.x) or bool(a.y)
 def __neg__(a):return A(-a.x,-a.y)
 def __add__(a,b):b=A(b);return A(a.x+b.x,a.y+b.y)
 __radd__=__add__
 def __sub__(a,b):return a+-A(b)
 def __rsub__(a,b):return A(b)+-a
 def __mul__(a,b):
  b=A(b)
  if not a.y:return A(a.x*b.x,a.x*b.y)
  if not b.y:return A(a.x*b.x,a.y*b.x)
  v=a.y*b.y;return A(a.x*b.x-KB*v,(a.x+a.y)*(b.x+b.y)-(a.x*b.x)-v-KA*v)
 __rmul__=__mul__
 def __truediv__(a,b):return a*inv(A(b))
 def __rtruediv__(a,b):return A(b)/a
 def __pow__(a,k):return A(1) if k==0 else (a*a)**(k//2)*(a if k%2 else 1)
def inv(s):
 if isinstance(s,F):return binv(s)
 if not s.y:return A(binv(s.x))
 x,y=s.x-s.y*KA,-s.y; d=binv(s.x*x-s.y*y*KB);return A(x*d,y*d)
Z=A(0);O=A(1)
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
def col(i,s):return [A(int(i==j)) for j in range(s)]
def span(P,U,v):return lin(solve(P,v),U)
def append(R,row):
 assert len(row)==len(R)+1
 for r in R:r.append(Z)
 R.append(row)
def padded(r,n):return r+[Z]*(n-len(r))

def cvalues(p):
 t=basis(1);j=basis(4);v=4*j/(33*t);big=(t+v)/2;sm=(t-v)/2
 assert 33*big**4-30*big**2+5==0 and 33*sm**4-30*sm**2+5==0
 return list(map(A,[F(0),(1-big)/2,(1-sm)/2,F(Q(1,2)),(1+sm)/2,(1+big)/2,F(1)]))
def pro(g,a,r,s):
 global KA,KB
 base=[[0],[Q(1,6),Q(1,6)],[Q(1,6),Q(1,3),Q(1,6)],[Q(1,4),0,0,Q(1,4)],[0,Q(27,22),Q(27,22),Q(-16,11),0]]
 B=[Q(11,120),Q(27,40),Q(27,40),Q(-8,15),Q(11,120)]
 q=6;G=[padded([a*x for x in row],5) for row in base];nodes=[sum(row,Z) for row in G];bs=[a*x for x in B]
 append(G,bs+[Z])
 # F(x)=x(x-a)(x-r). M_i(z)=integral F(x)x^i.
 def mom(z,i):return z**(i+4)/(i+4)-(a+r)*z**(i+3)/(i+3)+a*r*z**(i+2)/(i+2)
 P0=[mom(a,i) for i in range(3)];P1=[mom(r,i)-P0[i] for i in range(3)]
 pa,pb=solve([[P0[1],P1[1]],[P0[0],P1[0]]],[-P0[2],-P1[2]])
 assert not pa.y and not pb.y;KA,KB=pa.x,pb.x;v=A(0,1)
 P5=[e(Z,5),e(a,5),it(a,5),it(a,5,1),e(v,5)]
 U5=[col(0,7),col(5,7),padded(bs,7),padded([x*y for x,y in zip(bs,nodes)],7),col(6,7)]
 append(G,span(P5,U5,it(v,5)))
 P=[e(Z,6),e(a,6),it(a,6),e(v,6),e(r,6),e(s,6)]
 U=[col(0,9),col(5,9),padded(bs,9),col(6,9),col(7,9),col(8,9)]
 row=span(P,U,it(r,6));assert not row[-1];append(G,row[:8])
 append(G,span(P,U,it(s,6)))
 return G,(P,U),lambda y:span(P,U,it(y,6)),lambda y:span(P,U,e(y,6)),[5,7,8]
def ref(p,g):
 if p==11:
  a,b,d,c=[g[i] for i in (5,1,2,3)];t=[Z,a,b,d,c];n=5
  R=[padded([Z],n),padded([a/2,a/2],n)]
  co=solve([e(v,4) for v in (Z,b,a,d)],it(d,4));k=co[2]/co[1]
  P3=[e(v,3) for v in t[:3]];U3=[col(i,n) for i in range(3)]
  r=span(P3,U3,[z+k*u for z,u in zip(it(b,3),it(a,3))]);R.append([z-k*u for z,u in zip(r,R[1])])
  B=[z+k*u for z,u in zip(e(b,4),e(a,4))];Cb=[z+k*u for z,u in zip(col(2,n),col(1,n))]
  P=[e(Z,4),B,e(d,4),e(c,4)];U=[col(0,n),Cb,col(3,n),col(4,n)];R.append(lin([co[0],co[1],co[3]],U[:3]));R.append(span(P,U,it(c,4)))
  return t,R,(lambda y:span(P,U,it(y,4))),[2,3]
 a,b,d,c,u,v=[g[i] for i in (6,1,2,3,4,5)];t=[Z,a,b,d,c,u,v];n=7
 R=[padded([Z],n),padded([a/2,a/2],n)]
 R.append(span([e(w,3) for w in t[:3]],[col(i,n) for i in range(3)],it(b,3)))
 hh=[e(Z,4),e(b,4),it(b,4),e(d,4)];hhR=[col(0,n),col(2,n),R[2],col(3,n)]
 co=solve(hh,it(d,4));k=co[2];R.append(lin(co,hhR))
 P4=[e(w,4) for w in (Z,b,d,c)];U4=[col(i,n) for i in (0,2,3,4)]
 B=[z-k*y for z,y in zip(e(d,5),e(b,5))];Ub=[z-k*y for z,y in zip(col(3,n),col(2,n))]
 h4=[e(Z,5),B,e(c,5),e(b,5),e(u,5)]
 co=solve(h4,it(u,5));h=co[3]/co[2]
 row=span(P4,U4,[z+h*y for z,y in zip(it(c,4),it(b,4))]);R.append([z-h*y for z,y in zip(row,R[2])])
 C=[z+h*y for z,y in zip(e(c,5),e(b,5))];Uc=[z+h*y for z,y in zip(col(4,n),col(2,n))]
 P5=[e(Z,5),B,C,e(u,5),e(v,5)];U5=[col(0,n),Ub,Uc,col(5,n),col(6,n)]
 R.append(lin([co[0],co[1],co[2],co[4]],U5[:4]));R.append(span(P5,U5,it(v,5)))
 return t,R,(lambda y:span(P5,U5,it(y,5))),[4,5]
def full(p):
 g=cvalues(p);m=len(g);weights=solve([e(t,m) for t in g],it(O,m))
 assert all(weights) and all(dot(weights,[t**j for t in g])==O/(j+1) for j in range(p))
 y,R,br,singles=ref(p,g);ri=len(y)
 ordinary=[j for j in range(1,m-1) if j not in singles];fy=list(reversed(ordinary));assert len(fy)==3
 G,_,bp,ep,ach=pro(g,*[O-g[j] for j in fy]);nf=len(G)
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
 assert len(b)=={11:14,12:16}[p] and not any(A[0]) and not any(a for i,row in enumerate(A) for a in row[i+1:])
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


go(11)
```

Finally these rational-polynomial operations check both consecutive determinant factors everywhere and the distinct endpoint-mass constraints, without division by an individual tested moment or by a putative diagonal.

```python
import sympy as s
x,h,g,W=s.symbols('x h g W');ks=[]
def dd(P):return s.integrate(s.cancel((P-P.subs(x,h))/(x-h)),(x,0,1))
for i in range(2,6):
 P=s.expand(x*(x-1)*s.jacobi(i,1,1,2*x-1)); J=s.integrate(P,(x,0,x))
 V=J.subs(x,h)-g*P.subs(x,h);D=dd(J)-g*dd(P)
 O=dd(J).subs(h,0)-g*(dd(P).subs(h,0)-W*s.diff(P,x).subs(x,0))
 ks.append((V,D,O))
for i in range(3):
 V,D,O=ks[i];v,d,o=ks[i+1]
 det=s.factor(V*d-D*v); pole=s.factor(s.resultant(O,o,g)); k=i+2
 e=s.cancel(det/(h*(h-1)*(k*(k+4)*g*g+4*g*h-2*g-h*h+h))); f=s.cancel(pole/((k+1)*(k+3)*2*W-1)); assert e.is_Rational and e and f.is_Rational and f
 print('Jacobi index',k,det,pole)

```
