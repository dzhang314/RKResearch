# Exact embedded weights on Stepanov's fixed 15-stage tableau

For the particular [Stepanov Zenodo 15429897 tableau](https://zenodo.org/records/15429897), the span of Butcher weight vectors has dimension 14 through order eight, 15 through order nine. Thus a one-dimensional space of output-weight changes preserves order eight, and no nonzero change preserves order nine on this fixed matrix. This is not a claim about the whole family or other 15-stage ERK methods.

For any primary method of order \(p\) and \(1\le k<p\), the column version of the left side minus the right side of Butcher's monomial condition \(D(k)\) is
\[
\mathbf r_k\coloneqq A^\top(\mathbf b\odot\mathbf c^{\odot(k-1)})
-\tfrac1k\,\mathbf b\odot(\mathbf1-\mathbf c^{\odot k}).
\]
If \(\mathbf r_k\ne0\), adding any nonzero multiple to \(\mathbf b\) gives distinct embedded weights of order at least \(p-k\). For \(n\coloneqq |t|\le p-k\), the vectors \(\mathbf c^{\odot(k-1)}\odot A\boldsymbol\Phi_t(A)\) and \(\mathbf c^{\odot k}\odot\boldsymbol\Phi_t(A)\) are weights for \([t]\#[\bullet]^{\#(k-1)}\) and \(t\#[\bullet]^{\#k}\), with factorials \((n+k)t!\) and \((n+k)t!/n\). Their primary output coefficients are \(1/((n+k)t!)\) and \(n/((n+k)t!)\), respectively. Substituting them gives \(\mathbf r_k\cdot\boldsymbol\Phi_t(A)=0\). This is a direct use of standard D-type identities, not a claim of priority.

For \(p=10\), \(\mathbf r_2\) is Stepanov's monomial \(\mathbf d_1\); \(\mathbf r_1=0\). Section 5 exhibits the opposite entries of \(\mathbf d_1\) on the same-node pairs \((7,13),(9,10),(11,12),(14,8)\), its only support. The exact replay checks nonvanishing and all 200 order-eight tree conditions. The standalone exact rank certificate uses the listed 15 tree rows, with 14 of order at most eight; specializing \(x=\sqrt3,\ y=\sqrt7,\ z=\sqrt{147+42y}\) to \(177,190,149\) modulo 227 gives determinant 76. The denominators are units; the square relations and degree-eight field basis established with the other exact checks justify reduction. An independent modular certificate gives 925110 at prime 1000187 with substitutions \(417021,2646,46803\).

The reason the direction fails at order nine admits a shorter explanation. Put \(t\coloneqq [[\bullet]^{\#4}]\) (order six) and let \(g_\ell\) be the difference of its derivative weights within pair \(\ell\), whose node is \(\xi_\ell\). The exact replay checks that all \(g_\ell\) are nonzero and that the four nodes are distinct. The oriented pair coefficients \(\lambda_\ell\) of \(\mathbf r_2\) satisfy \(\sum_\ell\lambda_\ell g_\ell\xi_\ell^j=0\) for \(j=0,1,2\), by testing \(t\#[\bullet]^{\#j}\). The Vandermonde determinant entails a nonzero \(j=3\) moment and gives \(\lambda_\ell\) proportional to \(1/(g_\ell\prod_{m\ne\ell}(\xi_\ell-\xi_m))\). The same argument applies to any pair-supported perturbation when one tree has nonzero differences on all the pairs.

[SciML's merged estimator](https://github.com/SciML/OrdinaryDiffEq.jl/pull/3755) agrees with the normalized exact direction through a rigorously bounded difference of \(9.729\times10^{-84}\) entrywise. The pinned decimal estimator error vectors have maximum absolute tree residual \(1.5\times10^{-83}\) through order eight, versus \(0.0007899947632186318\) on a ninth-order tree. Independent replay gives decimal determinant residue 772915 modulo 1000003 and certifies the exact radical matrix lies within \(4.869\times10^{-91}\) of the pinned decimals. The exact proof does not depend on this enclosure. [Stepanov §5](https://etna.ricam.oeaw.ac.at/vol.63.2025/pp609-626.dir/pp609-626.pdf#page=9) · [Pinned tableau](https://github.com/SciML/OrdinaryDiffEq.jl/blob/69f5033/lib/OrdinaryDiffEqExplicitTableaus/src/tableaus_high_order.jl#L6336-L6471).

The replay takes the original Zenodo coefficient file as its argument. It requires SymPy.

```python
"""Verify the fixed-tableau embedding certificate. Pass the Zenodo coefficient text as argv[1]."""
from hashlib import md5
from pathlib import Path
from functools import lru_cache
from math import prod
from sys import argv

file = Path(argv[1])
data = file.read_bytes()
assert md5(data).hexdigest() == 'be9e5e3ba1ff8ed21124ad285d7d2fd5'
rows = [list(map(int,r.split())) for r in data.splitlines()]
assert len(rows) == 135
trees = """()
(())
(()())
((()))
(()()())
((()()))
(()()()())
((()()()))
(((()())))
((()()()()))
(()()()()())
(()(()()()()))
(()()(()()()()))
(()()()(()()()()))
(()(()()()))""".split()
def det(M,P):
    M = [m[:] for m in M]
    d = 1
    for j in range(len(M)):
        k = next((k for k in range(j,len(M)) if M[k][j]),None)
        if k is None:return 0
        if j != k:
            M[j],M[k]=M[k],M[j]
            d=-d
        v=M[j][j]
        d=d*v%P
        for k in range(j+1,len(M)):
            a=M[k][j]*pow(v,-1,P)%P
            for i in range(j+1,len(M)):
                M[k][i]=(M[k][i]-a*M[j][i])%P
    return d%P

def prime(p):return all(p%k for k in range(2,1+int(p**.5)))
for P in filter(prime, range(11,2000)):
    if any(r[-1]%P==0 for r in rows):continue
    sq={}
    for k in range(P):sq[k*k%P]=k
    if 3 not in sq or 7 not in sq:continue
    x=sq[3]
    y=sq[7]
    if (147+42*y)%P not in sq:y=-y%P
    if (147+42*y)%P not in sq:continue
    z=sq[(147+42*y)%P]
    def decode(row):
        a,b,c,d,e,f,g,h,q=row
        v=63*a+63*b*x+63*c*y+63*d*x*y+3*e*z+(-2*f+7*h)*x*z+3*g*y*z+(f-2*h)*x*y*z
        return v*pow(63*q,-1,P)%P
    v=list(map(decode,rows))[30:]
    A=[v[i*(i-1)//2:i*(i+1)//2] for i in range(15)]
    @lru_cache(None)
    def phi(t):
        ts=[]
        level=0
        for j,ch in enumerate(t[1:-1],start=1):
            if ch=='(':
                if not level:k=j
                level+=1
            else:
                level-=1
                if not level:ts.append(t[k:j+1])
        branches=[[sum(a*u for a,u in zip(row,phi(q)))%P for row in A] for q in ts]
        return [prod(row)%P for row in zip(*branches)] if branches else [1]*15
    d=det(list(map(phi,trees)),P)
    if d:
        assert (P,x,y,z,d)==(227,177,190,149,76)
        print(P,x,y,z,d,[t.count('(') for t in trees])
        break
else:raise AssertionError('No certificate')
import sympy as s
x=s.sqrt(3); y=s.sqrt(7); z=s.sqrt(147+42*y)
K=s.QQ.algebraic_field(x,y,z)
x,y,z=map(K.from_sympy,(x,y,z))
def decode_exact(row):
    a,b,c,d,e,f,g,h,q=row
    v=63*a+63*b*x+63*c*y+63*d*x*y+3*e*z+(-2*f+7*h)*x*z+3*g*y*z+(f-2*h)*x*y*z
    return v/(63*q)
v=list(map(decode_exact,rows))[30:]
A=[v[i*(i-1)//2:i*(i+1)//2] for i in range(15)]
@lru_cache(None)
def cuts(t):
    ts=[]
    level=0
    for j,ch in enumerate(t[1:-1],start=1):
        if ch=='(':
            if not level:k=j
            level+=1
        else:
            level-=1
            if not level:ts.append(t[k:j+1])
    return ts
@lru_cache(None)
def apply(t):
    return [sum((a*u for a,u in zip(row,exact_phi(t))),K.zero) for row in A]
@lru_cache(None)
def exact_phi(t):
    return [prod(row,start=K.one) for row in zip(*map(apply,cuts(t)))] if t!='()' else [K.one]*15
c,b = [list(map(decode_exact, rows[a:a+15])) for a in (0,15)]
u = [
    sum((b[i]*c[i]*A[i][j] for i in range(j+1,15)),K.zero)
    - b[j]*(K.one-c[j]*c[j])/2
    for j in range(15)
]
assert [i+1 for i,e in enumerate(u) if e] == list(range(7,15))
u = [e/u[6] for e in u]
T=['()']
for n in range(2,10):
    def forests(r,k):
        if r==0:
            yield ''
            return
        for j in range(k,len(T)):
            t=T[j]
            d=t.count('(')
            if d>r:break
            for forest in forests(r-d,j):
                yield t+forest
    layer=['('+s+')' for s in forests(n-1,0)]
    if n<=8:T.extend(layer)
print(len(T), flush=True)
assert len(T)==200
def pairing(t):return sum((a*b for a,b in zip(u,exact_phi(t))),K.zero)
assert not any(map(pairing,T))
assert any(map(pairing,layer))
print('Exact kernel verified')
pairs=[(7,13),(9,10),(11,12),(14,8)]
cs=[decode_exact(rows[i-1]) for i,j in pairs]
assert all(c==decode_exact(rows[j-1]) for c,(i,j) in zip(cs,pairs))
g=[exact_phi('((()()()()))')[i-1]-exact_phi('((()()()()))')[j-1] for i,j in pairs]
ell=[K.one/(v*prod((c-w for w in cs if w!=c),start=K.one)) for v,c in zip(g,cs)]
assert all(u[i-1]==v/ell[0] and u[j-1]==-v/ell[0] for (i,j),v in zip(pairs,ell))
print("Barycentric formula verified")
for j in range(4):
    t='((()()()())'+'()'*j+')'
    h=pairing(t)
    print('Moment',j,K.to_sympy(h).evalf(10))
    assert bool(h)==(j==3)
```
