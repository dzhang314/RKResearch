"""Explicit rational construction, Cramer's small interpolation formulas, all rooted tests."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import permutations
from math import factorial, gcd, lcm, prod
import json
from pathlib import Path
import sys

ZERO, ONE = F(0), F(1)
U = factorial(9)

def unit(x):
    y = abs(F(x).numerator)
    if y == 0:
        return False
    while (d := gcd(y, U)) != 1:
        y //= d
    return y == 1

def paid(x):
    d = F(x).denominator
    while (g := gcd(d, U)) != 1:
        d //= g
    return d == 1

def dot(a,b):
    return sum((x*y for x,y in zip(a,b)), ZERO)

def det(M):
    return sum(((-1)**sum(k[i]>k[j] for i in range(len(k)) for j in range(i+1,len(k)))*
                prod(M[i][k[i]] for i in range(len(k)))
                for k in permutations(range(len(M)))), ZERO)

def cramer(M,b):
    d=det(M)
    assert unit(d) and paid(d), d
    return [det([[b[i] if j==k else M[i][j] for j in range(len(M))] for i in range(len(M))])/d
            for k in range(len(M))]
def trans(M):
    return [list(z) for z in zip(*M)]

def pad(a,n):
    return list(a)+[ZERO]*(n-len(a))

A=[list(map(F,r)) for r in [(),('1/3',),(0,'2/3'),('1/12','1/3','-1/12'),
    ('7/4',-9,'9/4',6),('-3/64','9/8','-9/64','-27/64','-1/64'),('-65/4',81,'9/4',-33,-1,-32)]]
b=list(map(F,('11/120',0,'27/40','27/40','1/12','-8/15','1/120')))
c=[sum(r,ZERO) for r in A]
h=[x*y for x,y in zip(b,c)]
A.append(b.copy())
P=[lambda d: F(0)**d, lambda d: ONE, lambda d: F(1,d+1), lambda d: F(1,d+2)]
vec=[pad([ONE],8),pad([ZERO]*7+[ONE],8),pad(b,8),pad(h,8)]
a=F(1,2)
lam=cramer([[f(j) for f in P] for j in range(4)],[a**(j+1)/(j+1) for j in range(4)])
A.append([dot(lam,z) for z in zip(*vec)])
P.append(lambda d: a**d)
vec=[pad(v,9) for v in vec]+[[ZERO]*8+[ONE]]
mt=[[f(j) for j in range(5)] for f in P]
Pico=trans([cramer(mt,z) for z in zip(*vec)])
assert all(dot([F(1,j+1) for j in range(5)],z)==pad(b,9)[i] for i,z in enumerate(zip(*Pico)))
assert [sum(r,ZERO) for r in A][-2:]==[ONE,a]

clocklist=[F(1),F(1,4),F(1,4),F(-1,2),F(1,3),F(2,3),F(3,2),F(1,2),F(3,4),F(1,4),F(1)]
w=[ONE,ONE,ONE,F(-1,23625),F(-729,1000),F(-729,1000),
   F(-1,23625),F(6,7),F(17408,23625),F(17408,23625)-2,F(481,7560)-1]
w0=F(481,7560)
xs=clocklist
ys=[1-x for x in xs]
N=len(xs)
assert all(x>0 or x<0 for x in xs)
assert all(dot(w,[x**k for x in xs])+(w0 if k==0 else 0)==F(1,k+1) for k in range(9))
S=(1,3,4,5,6,7)
bar={i:ONE/prod(xs[i]-xs[j] for j in S if i!=j) for i in S}
u=[ZERO]*N
u[1]=-ys[1]**2/2
for i in S:
    u[i]=u[1]*w[1]*xs[1]*ys[1]/bar[1] * bar[i]/(w[i]*xs[i]*ys[i])
assert all(dot(w,[xs[i]*ys[i]*u[i]*xs[i]**k for i in range(N)])==0 for k in range(5))
v=[y*y/2+u_i for y,u_i in zip(ys,u)]
L=[[ZERO]*N for _ in range(N)]
L[1][0]=ys[1]
for i in (2,3):
    L[i][1]=v[i]/ys[1]
    L[i][0]=ys[i]-L[i][1]
donors=(0,1,2,3)
M=[[ONE]*4,[ys[j] for j in donors],[ys[j]**2 for j in donors],[u[j] for j in donors]]
# Among the four available late unit sites, these three pay the required projection.
pivots=(4,5,6)  # x=1/3, 2/3, 3/2: change the omitted site below if needed.
def ff(k,x):
    return x*(1-x)*(x**k-F(6,(k+2)*(k+3)))
MF=[[w[i]*ff(k,xs[i]) for i in pivots] for k in range(1,4)]
need_e=[-sum(w[i]*ff(k,xs[i])*(dot(L[i],[y*y for y in ys])-ys[i]**3/3) for i in range(4)) for k in range(1,4)]
need_u=[-sum(w[i]*ff(k,xs[i])*dot(L[i],u) for i in range(4)) for k in range(1,4)]
ce=cramer(MF,need_e)
cu=cramer(MF,need_u)
for i in range(4,N-1):
    g3,l_u = (ce[pivots.index(i)],cu[pivots.index(i)]) if i in pivots else (ZERO,ZERO)
    row=cramer(M,[ys[i],v[i],ys[i]**3/3+g3,l_u])
    for j,z in zip(donors,row):L[i][j]=z
assert all(dot(r,[ONE]*N)==ys[i] and dot(r,ys)==v[i] for i,r in enumerate(L))
for k in range(1,4):
    assert sum(w[i]*ff(k,xs[i])*(dot(L[i],[y*y for y in ys])-ys[i]**3/3) for i in range(N))==0
    assert sum(w[i]*ff(k,xs[i])*dot(L[i],u) for i in range(N))==0

# Reverse to forward chronology and form the weighted transpose.
# Only first four reverse columns have live downstream entries, and their weights are units.
T=[[w[N-1-j]*L[N-1-j][N-1-i]/w[N-1-i] if L[N-1-j][N-1-i] else ZERO for j in range(N)] for i in range(N)]
xf=xs[::-1];wf=w[::-1]
assert all(all(z==0 for z in r[i:]) for i,r in enumerate(T))
assert not any(T[0]) and not any(r[0] for r in T)
K=[[sum((xf[i]**(j+1)/(j+1)-dot(T[i],[x**j for x in xf]))*Pico[j][k] for j in range(5))
    for k in range(9)] for i in range(N)]
assert K[0]==pad(b,9)   # the unused x=1 suffix row is precisely the forward endpoint.
B=[w0]+[ZERO]*6+[wf[0],ZERO]+wf[1:]
A1=[pad(r,9+N-1) for r in A]
for i in range(1,N):
    A1.append(K[i]+T[i][1:])
assert len(B)==len(A1)==19
assert all(all(z==0 for z in r[i:]) for i,r in enumerate(A1))
assert all(paid(x) for x in (*B,*(z for r in A1 for z in r)))

# Chronological quotient by equality of complete padded physical rows.
# Quotient locations are discovered only from already processed rows.
def merge_identical(A,b):
    index={}
    representatives=[]
    old_to_new=[]
    final_b=[]
    signatures=[]
    merges=[]
    for i,row in enumerate(A):
        coeff={}
        for j,a in enumerate(row[:i]):
            if a:
                k=old_to_new[j]
                coeff[k]=coeff.get(k,ZERO)+a
        key=tuple(sorted((k,a) for k,a in coeff.items() if a))
        if key not in index:
            index[key]=len(representatives)
            representatives.append(i)
            signatures.append(key)
            final_b.append(ZERO)
        else:
            merges.append((i+1,representatives[index[key]]+1,b[i]))
        old_to_new.append(index[key])
        final_b[index[key]]+=b[i]
    assert len(set(signatures))==len(signatures)
    n=len(representatives)
    M=[[dict(key).get(j,ZERO) for j in range(n)] for key in signatures]
    assert all(all(z==0 for z in r[i:]) for i,r in enumerate(M))
    assert len({tuple(r) for r in M})==n
    return M,final_b,merges

A1,B,merges=merge_identical(A1,B)
print('canonical literal row merges (removed, retained, transferred weight):',merges)
print('remaining padded rows are pairwise distinct:',len(A1))

@lru_cache(None)
def forest(n,i=(0,())):
    if n==0:
        return ((),)
    return tuple((b,)+r for j in range(max(1,i[0]),n+1) for b in tree(j)
                 if (j,b)>=i for r in forest(n-j,(j,b)))
@lru_cache(None)
def tree(n):return forest(n-1)
@lru_cache(None)
def sz(t):return 1+sum(map(sz,t))
@lru_cache(None)
def tf(t):return sz(t)*prod(map(tf,t))
S1=[[(j,a) for j,a in enumerate(r) if a] for r in A1]
@lru_cache(None)
def phi(t):
    A=[ext(u) for u in t]
    return [prod(q[i] for q in A) for i in range(len(S1))]
@lru_cache(None)
def ext(t):
    q=phi(t)
    return [sum((a*q[j] for j,a in r),ZERO) for r in S1]
def defect(t):return tf(t)*dot(B,phi(t))-1
for k,n_expected in enumerate((1,1,2,4,9,20,48,115,286),1):
    ts=tree(k)
    assert len(ts)==n_expected
    bad=[(t,defect(t)) for t in ts if defect(t)]
    assert not bad, (k,bad[:1])
    print(f'order {k}: {len(ts)} cleared rooted equations')
G=0
witnesses=[]
for t in tree(10):
    z=defect(t)
    if z and gcd(G,z.numerator)!=G:
        G=gcd(G,z.numerator)
        witnesses.append((t,z,G))
        if unit(G):break
print('exact-order gcd',G,'witnesses',witnesses)
assert unit(G)
exponents = []
denom = lcm(*(z.denominator for row in A1 for z in row), *(z.denominator for z in B))
d = denom
for prime in (2,3,5,7):
    e = 0
    while d % prime == 0:
        d //= prime
        e += 1
    exponents.append(e)
assert d == 1
print("common denominator", denom, "exponents at (2,3,5,7)", exponents)
print("forward projection determinant", det(mt), "receiver local determinant", det(M),
      "high-moment determinant", det(MF))
print(len(A1),'physical rows, exact ninth order after every nonzero base change')
witness = ((), (), (), ((), (), (), (), ()))
assert sz(witness) == 10 and tf(witness) == 60 and defect(witness) == F(1,288)
expected = {'A': [[str(z) for z in row[:i]] for i,row in enumerate(A1)],
            'b': [str(z) for z in B],
            'coefficient_common_denominator': str(denom),
            'defect_tree': witness, 'defect': '1/288'}
path = Path(__file__).with_name('tableau.json')
if '--write-tableau' in sys.argv:
    path.write_text(json.dumps(expected, indent=2) + "\n")
else:
    assert json.loads(path.read_text()) == json.loads(json.dumps(expected))
