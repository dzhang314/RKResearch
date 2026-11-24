# Exact replay: nineteen split tests, full ordinary product response and mutual repair

This Python 3 / SymPy transcript uses rational arithmetic and polynomial remainders, no floating point. The large example is a true midpoint extrapolation method at the variable-diagonal p20/s55 endpoint, not a strict SDIRK. The four small examples are genuine strict common-diagonal RK tableaux. In the two algebraic controls choose any real root of the indicated irreducible polynomial; their common diagonal is nonzero.

```python
from fractions import Fraction as F
from functools import lru_cache
from math import prod
import sympy as S

# Exact 55-stage, order-20 variable-diagonal midpoint extrapolation.
m=10
nodes=[F(1,q*q) for q in range(1,m+1)]
W=[prod(-v/(u-v) for v in nodes if v!=u) for u in nodes]
assert [sum(w*u**a for w,u in zip(W,nodes)) for a in range(m)]==[1]+[0]*(m-1)
pts=[(q,j) for q in range(1,m+1) for j in range(q)]
n=len(pts); e=[F(1)]*n
c=[F(2*j+1,2*q) for q,j in pts]
b=[W[q-1]/q for q,j in pts]
d=[-F(1,4*q*q) for q,j in pts] # diagonal of R
A=[[F(1,2*q) if (q,j)==(u,k) else F(1,q) if u==q and k<j else F(0) for u,k in pts] for q,j in pts]
def mv(M,v):return [sum(x*y for x,y in zip(r,v)) for r in M]
dot=lambda a,b:sum(x*y for x,y in zip(a,b))
rho=[B*D for B,D in zip(b,d)]
assert mv(A,e)==c
for i in range(n):
 for j in range(n):
  assert (c[i]-c[j])*A[i][j]-sum(A[i][k]*A[k][j] for k in range(n))==(d[j] if i==j else 0)
ac=mv(A,c);f=[2*t*t-u for t,u in zip(c,ac)]; af=mv(A,f)
assert all(sum(f[i]*b[i]*A[i][j] for i in range(n))+af[j]*b[j]-dot(b,f)*b[j]==rho[j] for j in range(n))
assert all(rho)
D=2*m-2
@lru_cache(None)
def moment(k,j):
 return sum(B*L**k*t**j for B,L,t in zip(rho,d,c))
assert all(moment(k,a-2*k)==0 for a in range(D) for k in range(a//2+1))
assert moment(0,D)!=0
# C^18 is already a shortest nonzero word on this example.
assert S.Matrix(D+1,D+1, lambda i,j:moment(0,i+D-j)).det()==moment(0,D)**(D+1)
profile=[]
for a in range(D+1):
 h=D-a
 P=S.Matrix(a//2+1,h//2+1,lambda i,j:moment(i+j,D-2*i-2*j))
 profile.append(P.rank())
assert profile==[1,1,2,2,3,3,4,4,5,5,5,4,4,3,3,2,2,1,1] and sum(profile)==55
print('midpoint rational p20: support, short word, minimum-budget coefficient, graded ranks, sum')
print(n,'C^18',moment(0,D),profile,sum(profile))

# Literal bR c and bC R1 projected cross ranks at p=2, q=2, with both paid
# diagonal packets zero. These four controls are strict real tableaux.
def fixture(aa,bb,reduce=lambda x:S.factor(x)):
 A=S.Matrix(aa);b=S.Matrix([bb]);s=A.rows;e=S.ones(s,1);c=A*e;C=S.diag(*c);R=C*A-A*C-A*A
 ev=lambda v:reduce(v[0])
 assert [ev(b*e),ev(b*c),ev(b*C*c),ev(b*A*c)]==[1,S.Rational(1,2),S.Rational(1,3),S.Rational(1,6)]
 assert ev(b*R*e)==0
 u,v=ev(b*R*c),ev(b*C*R*e)
 k=int(u!=0),int(v!=0);lower=1+2-min(k)
 assert lower==s
 print('strict control',s,'crosses',u,v,'ranks',k,'lower',lower)
 return k
Q=S.Rational;H=Q(1,2)
k1=fixture([[H,0,0],[H,H,0],[Q(9,2),-3,H]],[Q(10,9),-Q(1,6),Q(1,18)])
k2=fixture([[H,0,0],[-Q(7,2),H,0],[-Q(9,14),Q(15,7),H]],[Q(62,63),Q(1,210),Q(1,90)])
g=S.symbols('g')
def modp(poly):
 def reduce(x):
  n,d=S.together(x).as_numer_denom()
  return S.rem(S.rem(n,poly,g)*S.invert(d,poly,g),poly,g).expand()
 return reduce
k3=fixture([[g,0],[1-2*g,g]],[H,H],modp(6*g**2-6*g+1))
delta=1/(6*(2*g-1)**2)
k4=fixture([[g,0,0],[H-g,g,0],[2*g,1-4*g,g]],[delta,1-2*delta,delta],modp(24*g**3-36*g**2+12*g-1))
assert [k1,k2,k3,k4]==[(0,1),(1,0),(1,1),(0,0)]

# A finite Toeplitz window can see strict losses beyond the first window.
t=S.symbols('t')
for u,v in [(2,3),(3,2),(2,2),(1,4)]:
 # PSD-shape is not intended: these are algebraic two-parity series,
 # separate from the genuine RK fixtures above.
 E=S.Matrix([[t**u,t**(u+v)],[0,t**v]])
 for h in range(1,6):
  def entry(i,j):
   k=i//2-j//2
   return E[i%2,j%2].expand().coeff(t,k) if k>=0 else 0
  T=S.Matrix(2*h,2*h,entry)
  assert 2*h-T.rank()==min(u,h)+min(v,h)
print('Toeplitz sample: 20 windows passed')
```

Observed exit 0. At p20 the short word is C^18 with coefficient -5749691557/5509331116684738560000; all earlier tested weighted monomial coefficients vanish. The split ranks sum to 55, in the order shown. At p2/q2 the strict cross-rank pairs are (0,1),(1,0),(1,1),(0,0); the stage bound is met in each case, with 3,3,2,3 stages respectively. Twenty symbolic Toeplitz test windows passed.

Run after the preceding script for the rectangular case and literal joint cuts:

```python
# Odd p and odd q: the larger crossing must carry an EXTRA direction.
qt=3; P=5
lev=[F(1,j*j) for j in range(1,qt+1)]
w=[prod(-z/(x-z) for z in lev if z!=x) for x in lev]
ds=[(F(2*k+1,2*j),-F(1,4*j*j),w[j-1]/j) for j in range(1,qt+1) for k in range(j)]
def porter(i,j,n):
 return sum(b*t**(i+j)*g**n for t,g,b in ds)
assert all(porter(i,j,(P-i-j)//2)==0 for i in range(3) for j in range(3) if (P-i-j)%2==0)
u=S.Matrix([[porter(i,j,(P+1-i-j)//2) for j in (0,2)] for i in (0,2)])
v=S.Matrix([[porter(1,1,2)]])
assert (u.rank(),v.rank())==(2,1)
assert (5+1+1-min(v.rank(),u.rank()-1))==len(ds)==6
print('rectangular q3/p5 on full-order-6 tableau',u.det(),v.det(),'price',len(ds))

# Two literal 10x10 physical cut matrices at p20 on the same 55 stages.
for upper in [True,False]:
 idx=list(range(0,10,2))+list(range(1,10,2))
 zeta=(9 if upper else 11); eta=20-zeta
 def packet(i,j):
  a=(10 if i%2==0 else zeta); bb=(10 if j%2==0 else eta)
  k=(a-i)//2+(bb-j)//2
  return sum(B*L**k*t**(i+j) for B,L,t in zip(b,d,c))
 Pmat=S.Matrix([[packet(i,j) for j in idx] for i in idx])
 assert Pmat.rank()==10
 assert (Pmat[5:,:5] if upper else Pmat[:5,5:])==S.zeros(5)
 print('literal p20 physical 10x10 cut; odd row grade',zeta,'rank',Pmat.rank())
```

Observed extra lines: rectangular determinants 1/14929920 and -1/6912, price 6; both literal p20 square products have rank 10 and the indicated off-diagonal zero block. Exit 0.


Additional exact first-response delay checks, to run after the original script. The sentinel 100 in this small test means the reachable word span was exhausted through dimension s, hence the response is identically zero.

```python
# Actual output/input deadlines, using all scalar A,C words and no eigenvalues.
def deadlinecase(aa,bb,reduce=lambda x:S.factor(x)):
 A=S.Matrix(aa);B=S.Matrix([bb]); s=A.rows;e=S.ones(s,1); c=A*e;C=S.diag(*c)
 R=C*A-A*C-A*A;P=A*R-R*A;d=B*(A+C)-B
 def mvlist(mats,cb):
  v=[e]; 
  for n in range(s+1):
   if any(reduce(cb(z))!=0 for z in v): return n
   v=[Y*x for Y in mats for x in v]
  return 100
 def rvlist(mats,cb):
  v=[B];
  for n in range(s+1):
   if any(reduce(cb(z))!=0 for z in v): return n
   v=[x*Y for Y in mats for x in v]
  return 100
 # p=3, two rows, thresholds D-i=1-i.
 out=[mvlist((A,C),lambda v:(B*C**i*R*v)[0])-(1-i) for i in range(2)]
 inp=[rvlist((A,C),lambda v:(v*R*C**i*e)[0])-(1-i) for i in range(2)]
 corr=mvlist((A,C),lambda v:((d*R-B*P)*v)[0])
 assert min(out+inp)>=0 and max(sum(out),sum(inp))<=2*s-4
 assert out[1]>=min(out[0],corr)
 print('strict p3 output/input/cubic-correction deadline slack',out,inp,corr)
 return out,inp
deadlinecase([[H,0,0],[H,H,0],[Q(9,2),-3,H]],[Q(10,9),-Q(1,6),Q(1,18)])
deadlinecase([[H,0,0],[-Q(7,2),H,0],[-Q(9,14),Q(15,7),H]],[Q(62,63),Q(1,210),Q(1,90)])
deadlinecase([[g,0],[1-2*g,g]],[H,H],modp(6*g**2-6*g+1))
deadlinecase([[g,0,0],[H-g,g,0],[2*g,1-4*g,g]],[delta,1-2*delta,delta],modp(24*g**3-36*g**2+12*g-1))
```

Observed p3 (out delays, in delays, correction delay): ([1,0],[0,1],0); ([0,1],[0,0],0); ([0,0],[0,0],100); ([1,1],[1,1],100). Exit 0.
