# Order 16 needs at least 25 explicit stages: final finite-rank certificate

**Candidate for independent audit.** A real, strictly lower triangular, classical order-16 RK tableau cannot have 24 stages. The f7=8 branch is excluded by erk_odd_even_joint_pencil_extensions_20261123.md; all earlier f7=7 cases except one are excluded in erk_order16_short_horizon_two_profiles_20261123.md. This closes the sole remaining simple-15 chart with an exact, small determinantal certificate. The proof/runs below are over characteristic zero except for explicitly justified reductions.

The chart consists precisely of fifteen simple d rows T, three hidden interior rows, the terminal, and five W rows at distinct c-nodes, one of them zero. Let p(x) denote the nonzero trace polynomial of degree at most four, formerly q(x)=Q(1−x) in the preceding note. On T, w_i=p(c_i); at W, p(c_i)≠0. Thus stage one, whose defects all vanish, cannot be in T because p(0)≠0. It is neither in the interior hidden set nor terminal, so it is precisely the unique zero W node. List the other four W nodes in stage chronology. Denote the first by u and the last by z, and set v=1−z. They are distinct; neither is 0 or 1 (Yb≠0 at W). Hence u and v are both nonzero and neither is 1.

At the first nonzero W row the known forward degree-two primitive, tested with x and x², gives ∫₀ᵘ x p=∫₀ᵘ x² p=0. At the last W row the reverse H=7 primitive, tested with 1 and y in y=1−x, gives ∫_z¹ (1−x)p=∫_z¹(1−x)² p=0. The reverse primitive is valid for these tests because deg Q≤4, deg P≤3, and 2+4+1=3+3+1=7. If Z4 is the four nonzero W-node polynomial, then
    ∫₀¹ x(1−x) p(x) Z4(x) x^j dx=0    (j=0,…,5).
This is the global W identity through degree 10 tested with the full W-node polynomial x Z4 times x^j. Hence p Z4 has at least six sign-changing roots in (0,1), as it is orthogonal to P5 for a positive measure and is nonzero of degree≤8. If u<0 the two left moments require at least two distinct roots of p strictly between u and 0; together with u, a root of Z4, these would give at least three noninterior roots, impossible. Likewise z>1 is impossible by the two right moments. Thus u,v>0 (no assumption of monotone stages or wholly interior nodes).

Write p=Σ_(i=0)^4 q_i x^i, and set M(u,v) to the 4×5 matrix whose rows for j=0,1 are respectively
    u^i/(i+j+2);    Σ_(a=0)^i binom(i,a)(−v)^a/(a+j+2).
Those are the two left and two right moment rows after scaling their lengths, so Mq=0. Define Q_i=(−1)^i det(M with column i removed)/(uv). They are rational-coefficient polynomials (the divisions are exact; u,v≠0 here). If M has rank four, p is proportional to the nonzero vector Q. If M has smaller rank, all Q_i vanish, so the following necessary determinantal constraints still hold without any division by a possibly zero cofactor.

The node factor Z4 is (x−u)(x−z)Z2 with Z2 a nonzero quadratic. Let β_j=1/[(j+2)(j+3)], the moments of x(1−x). Define
    D_j=Σ_i Q_i [β_(i+j+2)−(u+z)β_(i+j+1)+uz β_(i+j)]    (j=0,…,7).
The 6×3 Hankel matrix [D_(j+k)] for j=0,…,5 and k=0,…,2 has rank≤2. If M has rank four this is the six orthogonality equations above for Z2, and if not the Hankel matrix is identically zero. Thus all 20 maximal minors vanish. These equations are also necessary after interchanging u and v: reflect x↦1−x, interchanging the two left and two right moments, and use the symmetric measure x(1−x)dx. The reflected node polynomial has the four reflected original nonzero nodes, factors at v and 1−u, and the same degree-five orthogonality. This symmetry of the necessary equations does not require the reflected tableau itself to be a method or the zero W node to reflect to zero.

## Exact elimination

Take all 20 Hankel 3×3 minors in lexicographic row-triple order. Clear each minor’s rational denominator and divide the resulting integer polynomial by its positive coefficient gcd. Make three fixed integer linear combinations F_t by weighting the i-th normalized minor by (i+1)^t, for t=2,3,5 and i starting at 0. Each combination has degree at most 21 separately in u,v, checked during polynomial formation. Compute the binary degree-(21,21) resultants in v of (F2,F3) and (F2,F5). These necessary univariate eliminants have degree at most 42·21=882 in u by the Sylvester determinant. Both were computed OVER THE INTEGERS by exact interpolation at all 883 integers 0,…,882. Each sampled univariate resultant is an exact integer subresultant with projective leading-zero correction. The polynomial interpolation is exact (integer forward differences divided by factorials, reconstructing in the falling-factorial basis). Both actual degrees are 630.

Define
    T(x)=432x⁶−1440x⁵−160x⁴+4840x³−6300x²+3250x−625,
    B(x)=(x−1)^36 (8x−5)^9 T(x)^9.
Both exact resultants divide by B with identically zero remainder. The two quotients have degree 531 and are coprime modulo 2003 and modulo 2011, preserving top degree. This is sufficient: a primitive nonconstant common factor over Q keeps its degree when the leading coefficient of the containing primitive polynomial is a unit. Thus any feasible u is a root of B; by the symmetry above, so is v. This filters the common base points of the cofactor construction rather than assuming the initial matrix has full rank.

T is irreducible over Q: its factor degrees mod 7 are 3+3, and mod 11 are 2+4, both reductions degree six; the two sets allow no common proper factor degree. Sturm’s theorem gives exactly one positive root τ; the signs in the standard Sturm chain at 0 are −,+,+,−,−,+,+ and at +∞ are +,+,+,+,+,−,+. Because u,v>0 and neither equals 1, each is either 5/8 or this *same* root τ. There are only four parameter pairs left.

Check these four fibers projectively, now using the original matrix M, not its cofactors. T has the simple root 5 modulo 37 (T′(5)=3 modulo 37), so we may reduce τ to 5, and 5/8 to 33. The defining matrices and Beta moments have 37-unit denominators. If a complex projective solution q and Z2 existed at one of the four algebraic parameter pairs, one exists algebraically over the parameter field by elimination over its algebraic closure. Extend the chosen 37-adic place to the solution field; scale q and Z2 separately to have integral coordinates not all in the maximal ideal. Their reductions would give a nonzero projective solution over the residue algebraic closure, since all equations are homogeneous separately in these two vectors. This is why exceptional fibers may be excluded by a finite residue computation, independent of affine denominator worries.

At the three pairs containing 5, M mod 37 has one-dimensional kernel and its generator’s 6×3 Hankel matrix has rank three. At (33,33) the kernel has dimension two. In affine projective coordinate λ, the cubic minors from q=q0+λq1 have gcd 1; the missing infinite point q1 alone has rank three. Thus the special fibers contain no projective algebraic solution. All possible parameters are excluded. Together with the preceding short-horizon reductions this gives the asserted 25-stage lower bound.

## Replay of the two exact resultants

Only Python, SymPy and standard multiprocessing are needed. The degree-882 Newton interpolation is exact, not inferred from numerical evaluation or a modulus. The replays were executed in the cloud on November 23; no external research dispatch.

~~~python
import sympy as s,itertools as it,math,time
from sympy.polys.rings import ring
from sympy.polys.domains import QQ,ZZ
R,u,v=ring('u,v',QQ)
def integral(k):return QQ(1,(k+2)*(k+3))
def comb(i,j):return math.comb(i,j)
def det(A):
 n=len(A);return sum((-1)**sum(i>j for k,i in enumerate(p) for j in p[k+1:])*math.prod(A[j][i] for j,i in enumerate(p)) for p in it.permutations(range(n)))
M=[[u**i*QQ(1,i+j+2) for i in range(5)] for j in [0,1]]+[[sum((-v)**k*comb(i,k)*QQ(1,j+k+2) for k in range(i+1)) for i in range(5)] for j in [0,1]]
Q=[(-1)**i*det([[r[k] for k in range(5) if i!=k] for r in M]).exquo(u*v) for i in range(5)]
z=1-v
mom=[sum(c*(integral(i+j+2)-(u+z)*integral(i+j+1)+u*z*integral(i+j)) for i,c in enumerate(Q)) for j in range(8)]
hs={r:det([[mom[i+j] for j in range(3)] for i in r]) for r in it.combinations(range(6),3)}
from sympy.polys import euclidtools as ET
U,V=s.symbols('u v')
# clear denominators separately for all minors, taking primitive integers
J=[]
for f in hs.values():
 L=math.lcm(*(int(c.denominator) for c in f.values()))
 cf={ij:int(c*L) for ij,c in f.items()};content=math.gcd(*map(abs,cf.values()))
 J.append({ij:c//content for ij,c in cf.items()})
rng=([pow(i+1,j) for i in range(20)] for j in (2,3,5,6))
A=[]
for cs in rng:
 f={key:sum(c*h.get(key,0) for c,h in zip(cs,J)) for key in {(i,j) for h in J for i,j in h}}
 A.append([[f.get((i,j),0) for i in range(22)] for j in range(22)])
def ev(c,u):
 h=0
 for a in c[::-1]:h=h*u+a
 return h
def resultant(A,B,u):
 a=[ev(row,u) for row in A][::-1]
 b=[ev(row,u) for row in B][::-1]
 m=next((i for i,v in enumerate(a) if v),22);n=next((i for i,v in enumerate(b) if v),22)
 if m and n or m==22 or n==22:return 0
 factor=(-b[0])**m if m else a[0]**n
 return int(ET.dup_resultant(a[m:],b[n:],s.ZZ))*factor
from sympy.polys.galoistools import gf_gcd
from sympy.polys.domains import ZZ
from concurrent.futures import ProcessPoolExecutor
D=882
def dojob(v):
 i,j,u=v
 return resultant(A[i],A[j],u)
def interpolate(vals):
 xs=vals.copy();fact=1;coef=[]
 for i in range(D+1):
  a,r=divmod(xs[0],fact);assert not r
  coef.append(a); xs=[x-y for x,y in zip(xs[1:],xs[:-1])];fact*=i+1
 while coef and not coef[-1]:coef.pop()
 h=[coef[-1]]
 for i in reversed(range(len(coef)-1)):
  h=[b-i*a for b,a in zip([0]+h,h+[0])];h[0]+=coef[i]
 return s.Poly.from_list(h[::-1],U,domain=s.ZZ)
tau=432*U**6-1440*U**5-160*U**4+4840*U**3-6300*U**2+3250*U-625
B=s.Poly((U-1)**36*(8*U-5)**9*tau**9,U,domain=s.ZZ); allH=[]
for pairs in [(0,1),(0,2),(1,3)]:
 tt=time.monotonic()
 with ProcessPoolExecutor(max_workers=4) as pool:
  vals=list(pool.map(dojob,((pairs[0],pairs[1],u) for u in range(D+1)),chunksize=8))
 H=interpolate(vals)
 quot,rem=s.div(H,B)
 assert rem.is_zero
 print('pair',pairs,'degree',H.degree(),'quotient',quot.degree(),'time',time.monotonic()-tt,flush=True)
 allH.append(quot)
 for p in [2003,2011]:
  h=allH[0].set_modulus(p)
  for f in allH:
   assert f.set_modulus(p).degree()==f.degree()
  for f in allH[1:]:h=s.gcd(h,f.set_modulus(p))
  print('prime',p,'n',len(allH),'quotient-gcd degree',h.degree(),flush=True)
 if len(allH)>1 and h.degree()==0:break
~~~

Observed primary results: (0,1) and (0,2) each gave degree 630, quotient degree 531. Gcd degrees after the second pair were 0 at both 2003 and 2011. Exact division by B produced zero remainder. The unused (1,3) fallback is not required.

## Replay of the four exceptional fibers

~~~python
import sympy as s, itertools as it, math
x=s.Symbol('x')
T=s.Poly(432*x**6-1440*x**5-160*x**4+4840*x**3-6300*x**2+3250*x-625,x)
def rr(M,p):
 A=[[int(x%p) for x in row] for row in M];i=0;piv=[]
 for j in range(len(A[0])):
  k=next((k for k in range(i,len(A)) if A[k][j]),None)
  if k is None:continue
  A[k],A[i]=A[i],A[k]
  inv=pow(A[i][j],-1,p);A[i]=[z*inv%p for z in A[i]]
  for k in range(len(A)):
   if k!=i:A[k]=[(z-A[k][j]*y)%p for z,y in zip(A[k],A[i])]
  piv.append(j);i+=1
  if i==len(A):break
 free=[j for j in range(len(A[0])) if j not in piv]
 ker=[]
 for j in free:
  q=[0]*len(A[0]);q[j]=1
  for i,k in enumerate(piv):q[k]=-A[i][j]%p
  ker.append(q)
 return ker
def solve(p,u,v):
 M=[[pow(u,i,p)*pow(i+j+2,-1,p)%p for i in range(5)] for j in [0,1]]+[[sum(pow(-v,k,p)*math.comb(i,k)*pow(j+k+2,-1,p) for k in range(i+1))%p for i in range(5)] for j in [0,1]]
 E=rr(M,p);n=len(E); assert 1<=n<=2
 z=(1-v)%p
 def B(i):return pow((i+2)*(i+3),-1,p)
 def mo(Q):return [sum(c*(B(i+j+2)-(u+z)*B(i+j+1)+u*z*B(i+j)) for i,c in enumerate(Q))%p for j in range(8)]
 def rankq(Q):
  H=mo(Q)
  return len(rr([[H[i+j] for j in range(3)] for i in range(6)],p))==0
 if n==1:return ('single',rankq(E[0]))
 if not rankq(E[1]):return ('infty!',False)
 L=list(map(s.Integer,mo(E[0])));H=list(map(s.Integer,mo(E[1])));N=[l+x*h for l,h in zip(L,H)]
 G=None
 for a in it.combinations(range(6),3):
  D=s.Poly(s.Matrix([[N[r+j] for j in range(3)] for r in a]).det(),x,modulus=p)
  G=D if G is None else s.gcd(G,D)
  if G.degree()==0:break
 return ('pencil',G.degree()==0, G.as_expr())
for p in s.primerange(31,1000):
 roots=[r for r in range(p) if T.eval(r)%p==0]
 if not roots:continue
 r0=int(5*pow(8,-1,p)%p);a=roots[0]
 if len(set([r0,a,0,1]))!=4:continue
 sol=[(u,v,solve(p,u,v)) for u in [r0,a] for v in [r0,a]]
 print('prime',p,'tau root',a,'sol',sol)
 if all(r[2][1] for r in sol):break
~~~

Observed p=37, τ→5, four parameter pairs:
    (33,33): projective pencil, finite-minor gcd 1, infinite point impossible;
    (33,5), (5,33), (5,5): one-dimensional q kernel, Hankel rank three.

Auxiliary exact checks:
~~~python
assert [g.degree() for g,k in T.set_modulus(7).factor_list()[1] for _ in range(k)]==[3,3]
assert sorted(g.degree() for g,k in T.set_modulus(11).factor_list()[1] for _ in range(k))==[2,4]
assert T.count_roots(0,s.oo)==1 and T.eval(5)%37==0
~~~
