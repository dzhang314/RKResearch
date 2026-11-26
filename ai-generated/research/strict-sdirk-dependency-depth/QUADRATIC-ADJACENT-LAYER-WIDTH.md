# Shifted beta-Hankel rank gives quadratic width in terminal adjacent layers

## 1. Statement and scope

Let R be a nontrivial commutative ring. Let (A,b) have literal rooted-tree order p >= 1. Give every physical stage a level in 1,...,N. Assume that all physical diagonal entries of A equal a prescribed scalar gamma, that B=A-gamma I has nonzero entries only from level j to level j+1, and that b is supported in level N. Let w_j be the number of physical stages in level j.

The following necessary lower bounds hold:
```
w_N     >= floor((p+1)/2),
w_(N-h) >= floor((p-h)/2)             (1 <= h <= p-2),
N       >= max(1,p-1),
s       >= floor((p+1)/2) + floor((p-1)^2/4)
         = floor(p^2/4) + (1 if p is odd, 0 otherwise).
```
If gamma=0, the stronger strict version is
```
w_(N-h) >= floor((p-h+1)/2)           (0 <= h <= p-1),
N       >= p,
s       >= floor((p+1)^2/4).
```
In fact the rank argument forces that many distinct predecessor clock labels at the indicated layer in the relevant residue field, not just index cardinality. It uses actual strict B support, so strict same-clock edges are not erased. It does not assume positivity, an ordering on R, a domain, invertibility of gamma, or characteristic zero. These are not stage floors for general DIRK, for arbitrary skipped-level edges, or for arbitrary output layers.

## 2. A paid shifted beta-Hankel matrix

Let $\mathbf c\coloneqq A\mathbf 1$. The $n$-vertex tall tree gives $n!(\mathbf b\cdot A^{n-1}\mathbf 1)=1$ for $n\le p$; in particular all integers 1,...,p are units. Every residue field therefore has characteristic zero or characteristic strictly greater than p. A stage forest expression in c, A, and componentwise products is paid by adding one root for b^T. It evaluates in the ideal by replacing c with X, A with J(X^d)=X^(d+1)/(d+1), and the readout with the functional I(X^d)=1/(d+1). This follows termwise by the literal tree gamma factorials. Thus B becomes J-gamma.

For h,k,a >= 0, define the actual scalar
```
M_(k,a) = [ b · ( (1−c)^k ⊙ B^h c^a ) ]/(k! a!).
```
Its maximum literal order is h+k+a+1. At that payment, expand (J-gamma)^h and use
```
J^ell X^a = a! X^(a+ell)/(a+ell)!,
I[(1-X)^k X^n] = k! n!/(n+k+1)!.
```
The beta formula is formal rational algebra: the polynomial endpoint identity I(U')=U(1)-U(0) applied to X^(n+1)(1-X)^k gives the recursion k/(n+1) times the moment at (n+1,k-1) for k>0; k=0 is the monomial payment. The largest factorial index is h+k+a+1. Consequently
```
M_(k,a) = u_(k+a+1),
u_d = sum_(ell=0)^h binom(h,ell)(-gamma)^(h-ell)/(d+ell)!
    = [z^(h+d)] (1-gamma z)^h E_p(z),
E_p(z) = sum_(n=0)^p z^n/n!.
```

## 3. Rectangular full rank with only one extra tap

For h>=1 and r>=1 take k=0,...,r, a=0,...,r-1. Every entry is paid at p>=M=h+2r. The matrix has full column rank over every residue field of R, so its maximal minors generate the unit ideal. This does not select one common unit minor over R.

Work over a residue field F and suppose there is a nonzero column kernel vector (v_a). Reverse it into Q(z)=sum_(a=0)^(r-1) v_a z^(r-1-a). With R1=1-gamma z, W=R1^h Q and E_M the exponential jet through M, the equations say that coefficients h+r,...,M of W E_M vanish: coefficient h+r+k is sum_a v_a u_(a+k+1). Set P to its truncation through degree h+r-1, so
```
P = W E_M modulo z^(M+1),       degree P <= h+r-1.
```
P is nonzero: the first nonzero coefficient of Q, in degree beta<=r-1, remains unchanged in W E_M (its other factors have constant coefficient 1) and survives the truncation.

Use the polynomial identity
```
U=R1 Q,    V=R1 Q' + h R1' Q,    U W'=V W,
```
with degree V<degree U. No factoring, roots, inversion of gamma, or cancellation of an initial power of z is needed. Form
```
L=U(P'-P)-VP.
```
The leading term of -UP cannot cancel with the two derivative terms, so L is nonzero and has degree at most (r-1+degree R1)+(h+r-1)<=M-1. On the other hand, differentiation loses at most one order of the congruence. As E_M'-E_M=-z^M/M!, we obtain
```
L = U W (E_M'-E_M) = 0 modulo z^M,
```
a contradiction. Here M<=p, and all coefficients of the jet and all formal derivatives exist over F, which has characteristic zero or greater than p. When h=0 one may take R1=1, regardless of gamma. If R1=1 (also when gamma=0), the identical argument with a square r-by-r block has M=h+2r-1 and degree L<=h+2r-2.

For reference, the alternative rational logarithmic-derivative argument makes the effect of an initial z^beta explicit. Divide W and P by z^beta and call the resulting denominator and numerator D and P0. The surviving contact is T=M-beta, degree P0<=h+r-1-beta, and degree rad(D)<=r-beta because the h identical linear factors add at most one irreducible factor. Both constant terms are nonzero. The residual (P0/D)'/(P0/D)-1 has order at least T but a nonzero numerator of degree at most degree P0+degree rad(D)<=h+2r-1-2beta, after taking a common denominator of the two radical polynomials. This also contradicts T=h+2r-beta. The direct polynomial proof above avoids this division and does not need to form radicals.

For gamma=0, or h=0 for any gamma, use just the square with k,a=0,...,r-1. Then M_(k,a)=1/(h+k+a+1)! (in the h=0 case regardless of gamma). Under p>=h+2r-1, multiply row k by (h+k+r)!. Its a-th entry is the evaluation at k of the monic polynomial product_(j=a+2)^r (h+k+j) of degree r-a-1. The determinant is a signed Vandermonde in 0,...,r-1 times paid factorial units, hence a unit already over R. For nonunit gamma in a general ring, reduction at a maximal ideal containing gamma also proves the strict width conclusion, though it does not claim that original square determinant is a unit.

## 4. Exact layer factorization and physical stage sum

Because b is supported only on level N and each actual nonzero B edge moves one level, the functional $\mathbf v\mapsto \mathbf b\cdot((\mathbf 1-\mathbf c)^{\odot k}\odot B^h\mathbf v)$ reads only entries on level $N-h$. If that level does not exist, this row is zero. Thus the matrix factors as L R0 through those physical indices; R0 at index i and a has entry c_i^a/a!, and L at k and i has entry its coefficient at coordinate i divided by k!. Distinct indices with the same clock have the same row of R0, so even grouping those indices preserves factorization. Residue-field rank r thus requires at least r different clocks on that level; in particular w_(N-h)>=r. One can omit stages with no actual B path to terminal b-support. The proof neither needs nor claims that an individual repeated-clock edge is distinguishable by the probes.

For h=0 use the square rank at r=floor((p+1)/2). For h>=1 and h<=p-2 use the rectangular rank at r=floor((p-h)/2). Nonzero rank with h=p-2 forces level N-h to exist when p>=3, which gives N>=p-1. For p=1,2 the h=0 rank requires a nonempty terminal layer; there are no other required levels. The selected h give distinct, disjoint physical layers, even though witnesses may vary with h. The sum is
```
floor((p+1)/2) + sum_(j=2)^(p-1) floor(j/2)
= floor((p+1)/2) + floor((p-1)^2/4).
```
When gamma=0 the square gives r=floor((p-h+1)/2) for h=0,...,p-1, proving N>=p and the strict sum floor((p+1)^2/4).

## 5. Relation to one or several local Hankel decorations

The [local size-m determinant](LOCAL-PREDECESSOR-TEST.md) has grade q=m^2, ideal kappa_m X^(q-1)(X-q gamma), and enforces m effective strict predecessor clock groups on a row whenever nonzero. For gamma=0 its single h-edge tap is exactly kappa_m q!/(q+h+1)!, paid at p>=q+h+1; in general its two-tap floor uses p>=q+h+2. This earlier observation controls local donor degree, whereas the present beta-Hankel matrix controls how many receiving/start clocks must exist. At donor-layer distance d from the terminal layer (so d=h+1 for a local decorated row reached after h strict edges), the earlier floor floor(sqrt(p−d−1)) for arbitrary common gamma is bounded above by the new floor floor((p−d)/2), but the donor-group information is not discarded or implied by large layer width alone. No two stage floors are added.

There is also a precise limitation of ordinary multiple-decoration cap words. For h edges and requests m_0,...,m_h with at least two positive terms, their leading literal grade is D=sum m_j^2+h. Even if one could pay their nonzero output at the minimal leading cost D+1, each positive request m_j already fits the one-decoration common-gamma budget m_j^2+(h-j)+2: the difference from D+1 is sum_(t!=j) m_t^2+j-1>=0. Thus these words do not improve a condition stated only in terms of per-layer maximum caps. They can enforce compatible decorated vertices on a single path, which is not supplied by separate maxima. The new quadratic estimate comes instead from the multiplicity of independent endpoint probes through a fixed layer.

| Order p | Earlier common one-decoration stage floor | Common beta-Hankel floor | Strict beta-Hankel floor |
|---:|---:|---:|---:|
| 1 | 1 | 1 | 1 |
| 2 | 1 | 1 | 2 |
| 3 | 2 | 3 | 4 |
| 4 | 3 | 4 | 6 |
| 5 | 4 | 7 | 9 |
| 6 | 6 | 9 | 12 |
| 7 | 8 | 13 | 16 |
| 8 | 10 | 16 | 20 |
| 9 | 12 | 21 | 25 |
| 10 | 14 | 25 | 30 |
| 11 | 17 | 31 | 36 |
| 12 | 20 | 36 | 42 |
| 13 | 23 | 43 | 49 |
| 14 | 26 | 49 | 56 |
| 15 | 29 | 57 | 64 |
| 16 | 32 | 64 | 72 |
| 17 | 35 | 73 | 81 |
| 18 | 39 | 81 | 90 |
| 19 | 43 | 91 | 100 |
| 20 | 47 | 100 | 110 |

The table does not establish attainability, stability, or a stage improvement outside the stated adjacent terminal-output topology.
