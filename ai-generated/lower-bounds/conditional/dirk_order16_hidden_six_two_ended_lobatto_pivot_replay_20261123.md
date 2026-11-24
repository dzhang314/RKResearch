# Exact replay: the two-ended Lobatto quintic with its actual ninth-grade leakage

Companion of dirk_order16_hidden_six_two_ended_lobatto_reflection_20261123.md. This certificate concerns only fixed rational polynomials and grid roots. It never reduces unknown RK coefficients. Let L8(x)=Legendre_8(2x-1). Grid G={0,1} union roots(L8'); phi(x)=x times the shifted order-seven Jacobi polynomial for x dx. The derivative roots are distinct and in (0,1); alternatively their modular simple splitting, nonzero endpoint evaluations and rational orthogonality suffice for this certificate. At every nonzero grid root phi is nonzero by the Christoffel observation in the proof or the finite computation below. If using rationally normalized monic versions of the Jacobi functions instead, the fourth row is multiplied by one nonzero constant and rank is unchanged.

For ordered distinct nonzero grid roots (a,d), the first three rows give I_a[xP], I_a[x²P], I_d[x(x-a)P]. The fourth row gives phi(d) I_a[x²(x-a)P] - phi(a) I_d[x²(x-a)P]. The backward quadruple is the same functionals of P(1-y) on its own ordered pair. Coefficients are in the localized integer ring of the grid splitting field, with leading coefficient of L8' and integers 1,...,9 inverted. Every homomorphism to a residue field at the chosen good prime sends the nine grid nodes to nine DISTINCT base-field nodes: the derivative has seven distinct roots, and none is 0,1. A hypothetical characteristic-zero rank failure at any four choices would make every six-row minor vanish at their reductions. The exhaustive rank results in either prime forbid this. This argument allows repeated choices ACROSS the two ends, possible endpoint pivots, arbitrary algebraic conjugacy, and larger coefficient fields by scalar extension. It does not require a labeling of the finite-field roots by the real ordering.

Output of standalone Python 3 using integer arithmetic only, rerun after the last edit:

~~~text
p grid 1033 [0, 1, 207, 235, 353, 517, 681, 799, 827]
rank counts {(5, 6): 144, (4, 6): 7, (6, 6): 2985} bad [] 0
p grid 1237 [0, 1, 357, 385, 421, 619, 817, 853, 881]
rank counts {(5, 6): 144, (4, 6): 7, (6, 6): 2985} bad [] 0
~~~

The first entry in each rank-count key is the rank for the six uncorrected rows (omit both fourth rows), the second the ultimate rank using the two leakage comparisons. At both primes 151 candidate tuples have deficient raw rank, so simply claiming six independent raw moments is unsupported. Two more independent checks at split primes 1249 and 1901 gave zero final failures as well.

~~~python
from math import comb
from itertools import permutations,product
from fractions import Fraction as F
import sys

def prime(p):
 return p>=2 and all(p%d for d in range(2,int(p**.5)+1))
def evalpoly(co,t,p):
 r=0
 for a in co[::-1]:r=(r*t+a)%p
 return r
def rank(A,p):
 A=[v[:] for v in A]
 n=0
 for j in range(len(A[0])):
  k=next((k for k in range(n,len(A)) if A[k][j]%p),None)
  if k is None:continue
  A[n],A[k]=A[k],A[n]
  q=pow(A[n][j],-1,p)
  for k in range(n+1,len(A)):
   d=(q*A[k][j])%p
   for l in range(j,len(A[0])):A[k][l]=(A[k][l]-d*A[n][l])%p
  n+=1
 return n

leg=[(-1)**(8-k)*comb(8,k)*comb(8+k,k) for k in range(9)]
jac=[(-1)**(7-k)*comb(7,k)*comb(8+k,7) for k in range(8)] # shifted Jacobi weight x; check k=0 gives -8, k=7 gives 6435
der=[i*leg[i] for i in range(1,len(leg))]
def run(p):
 assert prime(p) and p>17 and der[-1]%p!=0
 Z=[i for i in range(p) if evalpoly(der,i,p)==0]
 if len(Z)!=7 or 0 in Z or 1 in Z:return False
 Z0=[0,1]+Z
 print('p grid',p,Z0,flush=True)
 def rows(u,v):
  I=lambda u,n:pow(u,n+1,p)*pow(n+1,-1,p)%p
  h=lambda u:u*evalpoly(jac,u,p)%p
  assert h(u)*h(v)%p
  return [[I(u,i+1) for i in range(6)], [I(u,i+2) for i in range(6)],
    [(I(v,i+2)-u*I(v,i+1))%p for i in range(6)],
    [(h(v)*(I(u,i+3)-u*I(u,i+2))-h(u)*(I(v,i+3)-u*I(v,i+2)))%p for i in range(6)]]
 sides=list(permutations(Z0[1:],2))
 l={q:rows(*q) for q in sides}
 r={q:[[sum(row[k]*(-1)**k*comb(i,k) for k in range(i+1))%p for i in range(6)] for row in L] for q,L in l.items()}
 bad=[]; short=[];counts={}
 for a,b in product(sides,repeat=2):
  sc=rank(l[a][:3]+r[b][:3],p)
  rank8=rank(l[a]+r[b],p) if sc<6 else 6
  counts[sc,rank8]=counts.get((sc,rank8),0)+1
  if rank8<6:bad.append((a,b,sc,rank8))
 print('rank counts',counts,'bad',bad[:60],len(bad),flush=True)
 assert len(sides)==56 and sum(counts.values())==3136 and not bad
 return True
for p in [1033,1237]:
 assert run(p)
~~~
