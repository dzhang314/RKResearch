# Local predecessor-clock tests for adjacent-layer RK methods

The [quadratic stage floor](QUADRATIC-ADJACENT-LAYER-WIDTH.md)
is stronger as a stage-count bound. The test below instead locates a
single row with many distinct effective predecessor clocks, which
does not follow from a large layer width alone.

## Statement and scope

Let R be a nontrivial commutative ring and let (A,b) satisfy literal rooted-tree order p >= 1. Suppose every physical diagonal entry is a prescribed common scalar gamma, and give the physical stages levels 1,...,N. Write B=A-gamma I and c=A 1. For the adjacent-layer corollary assume that B(i,j) != 0 implies level(i)=level(j)+1, and that b is supported on level N. Let w_j be the number of physical stages in level j. Empty levels are allowed in the notation; the asserted witnesses force the indicated levels to be nonempty.

For every integer 1 <= k <= p-2 there is a row in level N-k+1 with at least floor(sqrt(p-k-1)) distinct effective strict predecessor clock groups, all in level N-k. Consequently
```
N >= max(1,p-1),
w_(N-k) >= floor(sqrt(p-k-1))                  (1 <= k <= p-2),
s >= 1 + sum_(j=1)^(max(0,p-2)) floor(sqrt j).
```
When gamma=0, the sharper literal strict version is
```
N >= p,
w_(N-k) >= floor(sqrt(p-k))                    (1 <= k <= p-1),
s >= 1 + sum_(j=1)^(p-1) floor(sqrt j).
```
These are necessary stage floors for this structured class, not attainment statements and not stage floors for general DIRK, arbitrary skipped edges, or tableaux with multiple output layers. There is no positivity, ordered-field, domain, gamma-invertibility, or characteristic-zero assumption.

A strict predecessor clock group of row i is a value z of c_j among strict predecessors, with aggregate sum of B(i,j) over its indices nonzero. The value z=c_i is allowed. Because B removes the *physical* diagonal only, strict same-clock edges are not erased; this is not a commutator support claim.

## 1. Literal grade and one shifted determinant

Literal tall conditions give n! (b · A^(n-1) 1)=1 for n<=p, so every integer from 1 through p is a unit. A stage forest has grade equal to the total size of its component trees. At the stage level, multiplication is grade-additive, A adds one, and c has grade one. Taking the inner product with b gives the tree readout and adds one to the forest grade. Expand finite sums and products into actual rooted forests to use literal order. The formal model for a paid stage expression replaces c by X and A by J, where J(X^e)=X^(e+1)/(e+1); output integration over [0,1] sends X^e to 1/(e+1). This is notation for factorial-cleared coefficients only. B therefore becomes J-gamma. Inhomogeneous expressions are expanded and paid term by term.

For m>=1 define the actual row decoration
```
Delta_m(i) = det[(B c^(a+b))_i]_(0<=a,b<m).
```
If row i has fewer than m effective strict predecessor clock groups, this determinant is zero: the moment matrix factors through those groups using column vectors (1,z,...,z^(m-1)), with the aggregate B weights on the intervening diagonal. This is a determinant factorization over R, with no division by differences of actual clock values. Put Delta_0=1.

Write q=m^2 and let kappa_m=det[1/(a+b+1)]_(0<=a,b<m). The decoration's maximum forest grade is q, and its exact ideal is
```
Delta_m^*(X)=kappa_m X^(q-1)(X-q gamma)
             =kappa_m q (J-gamma) X^(q-1).
```
To see the coefficient of gamma, at the ideal row change the moment basis from powers Y^a to powers (X-Y)^a on each side. The two triangular basis determinant signs cancel. The ideal row moments before subtracting gamma are X^(a+b+1)/(a+b+1); evaluation at Y=X is the first coordinate only in the new basis. Thus the gamma coefficient is minus the positive-index Cauchy cofactor times X^(q-1). The full Cauchy determinant divided by that cofactor is (prod_(a=1)^(m-1) a/(a+1))^2=1/q. The empty cofactor when m=1 is 1. All positive differences and arguments in these constant Cauchy determinants are at most 2m-1<=q, so kappa_m is a unit. The actual clock basis change is also valid, but the physical predecessor factorization above does not need it.

## 2. Two taps preserve a long physical path at linear cost in its length

Fix h>=0, m>=1, and put n=h+1. The two actual outputs are
```
Y_j=b · (c^j ⊙ B^h Delta_m),          j=0,1.
```
Their respective maximum literal orders are q+h+1 and q+h+2. The ideal stage expression is kappa_m q (J-gamma)^n X^(q-1). Its leading X coefficient is kappa_m q!/(q+h)!, a unit in the paid range.

At p>=q+h+2, both taps are available. For a=q or q+1 define the formal coefficient
```
G_a(gamma)=(q-1)! sum_(ell=0)^n binom(n,ell)(-gamma)^(n-ell)/(a+ell)! .
```
Expansion of (J-gamma)^n gives Y_0=kappa_m q G_q. For Y_1 use (q+ell)/(q+ell+1)!=1/(q+ell)!-1/(q+ell+1)!; hence Y_1=kappa_m q (G_q-G_(q+1)). The largest factorial argument here is q+n+1=q+h+2, not a larger analytic or interpolation payment.

The two outputs generate the unit ideal. Check any residue field of R. If gamma reduces to zero, G_q=(q-1)!/(q+n)! is nonzero. Otherwise, put x=1/gamma in that field. The identity
```
G_a=(q-1)! n!/(n+a)! * (-gamma)^n L_n^(a)(x),
L_j^(a)(x)=sum_(ell=0)^j binom(j+a,j-ell)(-x)^ell/ell!
```
reduces a common zero to one of L_n^(q) and L_n^(q+1). Pascal's identity gives L_n^(q+1)-L_n^(q)=L_(n-1)^(q+1). Consecutive degrees at the same parameter alpha=q+1 cannot both vanish: for j>=2,
```
j L_j^(alpha)=(2j+alpha-1-x)L_(j-1)^(alpha)
                 -(j+alpha-1)L_(j-2)^(alpha).
```
This is coefficientwise binomial algebra: with H=j+alpha-1 and k=j-ell, the identity after Pascal reduces to H binom(H-1,k-1)=k binom(H,k). The downward multipliers j+alpha-1 are units (at most n+q); descent reaches L_0=1. For n=1, Pascal already gives L_0=1. This establishes the unit-ideal claim over the paid ring, not an assertion that a chosen tap is always a unit. In particular at least one actual output is nonzero.

If gamma=0 it suffices to pay only Y_0, at p>=q+h+1: Y_0=kappa_m q!/(q+h+1)!, a unit. The same reduced payment forces Y_0 != 0 for any nonunit gamma in R, by reducing at a maximal ideal containing gamma. More generally at this lower payment the displayed first-tap coefficient suffices whenever G_q(gamma) is nonzero.

Expand the nonzero actual tap as a sum over h-edge paths. One summand is nonzero; hence its final b-weight, shifted-strict B edges, and initial Delta_m are all nonzero. This works with zero divisors. The initial row thus has at least m effective strict predecessor clock groups. No comparison of the signs of individual sums is used.

## 3. Piecewise layer caps, stage count, and comparison

For the layer statement set h=k-1. Since the terminal tap does not move the output and b is supported on level N, the decorated initial row is at level N-h=N-k+1. Its strict donors are all at level N-k. The exact order threshold is p>=m^2+k+1, or p>=m^2+k in the strict case. Taking the largest allowed m proves the square-root staircase. Existence at the last admissible k with m=1 forces N>=p-1 or N>=p, respectively; for p=1 and the common-diagonal p=2 case the nonzero final layer suffices. Different k count disjoint physical layers even if their witnessing paths and clocks differ. The terminal b-support adds at least one further stage because b^T 1=1.

Equivalently, if d_j caps the number of effective strict predecessor clocks of every relevant receiving row in level j, set d_1=0. Then
```
p <= min_(1<=j<=N) [(d_j+1)^2+N-j+1]       (common gamma),
p <= min_(1<=j<=N) [(d_j+1)^2+N-j]         (strict gamma=0).
```
For a cap only on the b-active rows this is generally unjustified: the initial decorated row can have b_i=0 and still be a strict ancestor of active output. Caps on those relevant ancestors suffice. If B is allowed to skip levels or the output uses several levels, the path statement still holds but the asserted individual level indices and sum of widths do not follow.

For context, the general decorated-word construction in the next section used with one nonzero decoration alone gives the weaker staircase floor(sqrt(p-2k)) and stage floor 1+sum_(k>=1,2k<p) floor(sqrt(p-2k)). The table compares these structured floors; the gamma=0 column is stronger than the uniform common-gamma column, and neither is a general DIRK stage result.

| p | General word, one decoration | Common gamma, two taps | Strict gamma=0, one tap |
|---:|---:|---:|---:|
| 1 | 1 | 1 | 1 |
| 2 | 1 | 1 | 2 |
| 3 | 2 | 2 | 3 |
| 4 | 2 | 3 | 4 |
| 5 | 3 | 4 | 6 |
| 6 | 4 | 6 | 8 |
| 7 | 5 | 8 | 10 |
| 8 | 6 | 10 | 12 |
| 9 | 7 | 12 | 14 |
| 10 | 8 | 14 | 17 |
| 11 | 10 | 17 | 20 |
| 12 | 11 | 20 | 23 |
| 13 | 13 | 23 | 26 |
| 14 | 14 | 26 | 29 |
| 15 | 16 | 29 | 32 |
| 16 | 17 | 32 | 35 |
| 17 | 19 | 35 | 39 |
| 18 | 21 | 39 | 43 |
| 19 | 23 | 43 | 47 |
| 20 | 25 | 47 | 51 |

Both sharpened stage floors are (2/3)p^(3/2)-O(p), by the elementary sum of sqrt(j) and loss of at most one per summand. The number of physical stages, not merely a depth statistic, is counted here only because the adjacent terminal-output hypothesis pinpoints disjoint donor layers.

## 4. General depth-varying decorated word (no recurrence needed)

For a word m_0,...,m_h of nonnegative donor requirements, start Z_0=Delta_(m_0) and set Z_j=Delta_(m_j) odot B Z_(j-1). Let D=sum_j m_j^2+h and u=# {j:m_j>0}. The ideal of Z_h is supported in powers X^(D-h-u),...,X^D: each use of the lower term of a nontrivial shifted decoration or of J-gamma drops degree by one. Its leading coefficient is the product of the kappa factors and the leading J integration units, all within D. Thus the h+u+1 taps b^T(c^k odot Z_h), k=0,...,h+u, cannot all vanish once
```
p >= sum_j m_j^2 + 2h + u + 1.
```
Indeed their coefficients in the indicated monomial span are a unit Cauchy matrix, with largest denominator D+h+u+1 and all positive differences at most h+u. Nonnegative starting exponent follows from sum m_j^2>=u. In the actual finite path expansion one nonzero term yields all requested row decorations along a single shifted-strict path. Each request m_j is therefore met by actual clock-aggregated predecessor groups at the corresponding path vertex.

If every B edge strictly increases layer, the path yields an increasing layer subsequence ending at a b-active layer, with cap there at least the prescribed m_j at each position. Under adjacency this is a consecutive layer window. If a given cap profile forbids such a subsequence/window, the achieved order is strictly below the displayed payment. Without layer assumptions this is a physical path witness only. A commutator alternative would erase strict same-clock edges and count only clock-changing donors; no such switch is made here.
