# Physical signed-defect pencil replay

Exact Python 3 and SymPy, concatenated into a single standalone run. The first portion constructs the same rooted-tree controls as in the companion on mutual parity repair. The actual pencil checks follow, including all 55 physical stages for the variable-diagonal control. All high-order abstract flag matchings are explicitly distinguished from actual RK tableaux.

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
# Direct characteristic-zero polynomial pencil checks on true small RK methods.
Z=S.symbols('Z')
def pencilcheck(A,b,red=lambda x:S.factor(x)):
 A=S.Matrix(A); b=S.Matrix([b]); n=A.rows; e=S.ones(n,1);c=A*e
 B=S.diag(*b);C=S.diag(*c);R=C*A-A*C-A*A;rho=(b*R).applyfunc(red);W=S.diag(*rho)
 M=(B*A+A.T*B-b.T*b).applyfunc(red)
 ids=[i for i in range(n) if rho[i]==0]
 aa=S.Poly(S.together((M-Z*W).det()-(-Z)**n*W.det()).expand(),Z)
 assert all(red(t)==0 for t in aa.all_coeffs())
 if ids: assert red(M.extract(ids,ids).det())==0
 else:
  L=(W.inv()*M).applyfunc(red)
  assert (L**n).applyfunc(red)==S.zeros(n)
 print('physical pencil',n,'blind indices (1-based)',[i+1 for i in ids])
 return ids
pencilcheck([[g,0],[1-2*g,g]],[H,H],modp(6*g**2-6*g+1))
pencilcheck([[g,0,0],[H-g,g,0],[2*g,1-4*g,g]],[delta,1-2*delta,delta],modp(24*g**3-36*g**2+12*g-1))
u=g; v=1-g;red=modp(6*g**2-6*g+1)
for mass in [-H,H]:
 a32=(v-Q(1,4))/(2*mass)
 aa=[[v,0,0],[u-Q(1,4),Q(1,4),0],[v-u-a32,a32,u]]
 bb=[H-mass,H,mass]
 pencilcheck(aa,bb,red)

# All 55 physical coefficient rows in a small exact factorization.
# K has one constant column per midpoint branch; M=K(diag(Wq)-w*w^T)K^T.
K=S.Matrix([[Q(1,q) if q==u else 0 for u in range(1,m+1)] for q,j in pts])
ww=S.Matrix(W);BX=S.diag(*b); Aix=S.Matrix(A);Mx=BX*Aix+Aix.T*BX-S.Matrix(b)*S.Matrix([b]); Dx=S.diag(*rho)
J=S.diag(*W)-ww*ww.T
assert Mx==K*J*K.T
gram=K.T*Dx.inv()*K
assert gram==S.diag(*[-4*i*i/W[i-1] for i in range(1,m+1)])
compact=J*gram
assert compact.charpoly(Z).as_expr()==Z**m and compact**m==S.zeros(m)
assert (compact**(m-1)).rank()==1 and compact.rank()==m-1
print('physical p20 signed-defect pencil nilpotent: exact index',m,'rank',m-1)

# Unconditional degree caps, with an exact combinatorial extremizer
# for the saturated FLAG data plus e extra unconstrained stages (not RK).
h=profile;D=18
for slack,cap in enumerate([0,20,36,48,56,60]):
 N=55+slack
 grades=[j for j,v in enumerate(h) for k in range(v)]+[D+1]*slack
 L=[[(j,k) for k in range(h[j])] for j in range(D+1)]
 ext=[(D+1,k) for k in range(slack)]
 grade_of=lambda a:a[0]
 inv={}
 for k,fresh in enumerate(ext):
  seq=[(j,k) for j in range(D+1) if k<h[j]]
  if not seq: inv[fresh]=fresh; continue
  inv[seq[0]]=fresh; inv[fresh]=seq[0]
  for j,a in enumerate(seq[1:],1):inv[a]=seq[len(seq)-j]
 for j in range(D+1):
  for k in range(slack,h[j]):inv[j,k]=(D-j,k)
 assert len(inv)==N and all(inv[inv[a]]==a for a in inv)
 assert min(grade_of(a)+grade_of(b) for a,b in inv.items())>=D
 achieved=sum(grade_of(a)+grade_of(b)>D for a,b in inv.items())
 required=sum(max(0,v-slack) for v in h)
 assert achieved==N-required==cap
 print('s, mandatory W, maximum M for abstract flags',N,required,achieved)
# The coarse p*slack is genuinely attained by a strict order-2 tableau.
aa=S.Matrix([[Q(1,3),0],[1,Q(1,3)]]);bb=S.Matrix([[Q(5,6),Q(1,6)]]);e2=S.ones(2,1);cc=aa*e2;CC=S.diag(*cc)
assert (bb*e2)[0]==1 and (bb*cc)[0]==H
RR=CC*aa-aa*CC-aa*aa;WW=S.diag(*(bb*RR));BB=S.diag(*bb);MM=BB*aa+aa.T*BB-bb.T*bb
assert MM.det()==-Q(1,81) and S.degree((WW+Z*MM).det(),Z)==2
print('strict p2/s2 nonlinear pencil degree',S.degree((WW+Z*MM).det(),Z))

```

Observed exit 0. The two small genuine mixed examples both gave blind set {2}. The normalized physical p20 variable-diagonal defect had rank 9 and nilpotence index 10. The p20 abstract allowed degrees for s=55,...,60 were 0,20,36,48,56,60, and the separate genuine p2/s2 strict method attained degree two.
