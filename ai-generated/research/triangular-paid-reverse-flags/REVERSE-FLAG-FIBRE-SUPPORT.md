# Hidden prefix pivots, later same-clock partners, and paid terminal stage order

Necessary support distribution for ordinary triangular RK, including
varying diagonals and unrestricted skip edges. Coefficients are in a
characteristic-zero field; weights may be signed, zero, and unordered.
The structural pivot hypotheses are explicit. No claim about an
unrestricted new stage floor or any individual algebraic chart.

## 1. Literal low context flags and physical pivots

Let \(A\) be lower triangular on \(s\) physical stages, \(e=1\),
\(c=Ae\), \(C=\operatorname{diag}(c)\), and let \((A,b)\) satisfy
rooted order through \(p\). Write \(s=p+k\).
The grade of \(\Phi(\tau)\) is \(|\tau|-1\); its exact polynomial is
\((|\tau|/\rho(\tau))X^{|\tau|-1}\), with tree factorial \(\rho\).
Let \(P_h\) be the stage span through grade \(h\), and \(Z_h\) the
actual image of formal linear combinations of those trees with zero
exact polynomial. The polynomial need not descend to a function on
all actual stage vectors.

An \(A\) applies formal integration and costs one grade by a unary
lift; a \(C\) multiplies by \(X\) and costs one grade by adding a leaf.
Componentwise product merges roots, adds grades and multiplies exact
polynomials. This follows directly from the tree factorial
\(\rho([\tau_1,\ldots,\tau_m])=|[\tau_1,\ldots,\tau_m]|
\prod \rho(\tau_i)\). Output on a paid model is integration from
0 to 1. In particular \(A\) and \(C\) carry \(Z_h\) into \(Z_{h+1}\).

Let \(\mathcal R_t\) be the actual row span of
\(b^T T_1\cdots T_r\), \(0\le r\le t,\ T_j\in\{A,C\}\).
An entry outside
\[
 J_t=\bigcup_{\lambda\in\mathcal R_t}\operatorname{supp}\lambda
\]
is jointly zero in the whole paid flag, not just in \(b^T\).
For each \(\lambda\in\mathcal R_r\),
\[
       \lambda(z\odot v)=0\quad
       (z\in Z_a,\ v\in P_d,\ a+d+r\le p-1).                 \tag{1}
\]
This includes rooted products of two defects. Each polynomial or
word expression is expanded before paying the maximum order; actual
scalar choices of diagonal and clock values in an expression are
allowed.

The following literal pivot mechanism supplies ranks used below.
At the first nonzero physical clock \(f\), one of
\[
          z_2=Ac-c^{\odot2}/2,\qquad
          z_3=A(c^{\odot2})-c^{\odot3}/3
\]
has its first nonzero entry at \(f\). All earlier entries of both are
zero by triangularity. At \(f\) their values are
\(c_f(A_{ff}-c_f/2)\) and \(c_f^2(A_{ff}-c_f/3)\).
Use seed grade \(a_0=2\) unless \(A_{ff}=c_f/2\), when take
\(a_0=3\). In particular \(a_0=2,f=1\) for a nonzero first
diagonal, and \(a_0=2,f=2\) for strict \(A\) with \(A_{21}\ne0\).

If \(z\) has first nonzero coordinate \(i\), both
\((A-A_{ii}I)z\) and \((C-c_iI)z\) vanish through row \(i\).
At row \(i+1\) their entries are
\[
 A_{i+1,i}z_i+(A_{i+1,i+1}-A_{ii})z_{i+1},
       \qquad (c_{i+1}-c_i)z_{i+1}.
\]
If \(A_{i+1,i}\ne0\) and either the adjacent diagonals agree or the
adjacent clocks differ, then at least one is nonzero. For equal
diagonals use the first; for different clocks use the second unless
\(z_{i+1}=0\), when the first works. Each step costs one defect grade.
Consequently the adjacent segment with this property gives leading
defect pivots \(f,\ldots,f+h-a_0\) through grade \(h\).
Their restrictions have independent columns on any subset of
those pivot rows, by the triangular pivot submatrix.
An adjacent equal-clock, unequal-diagonal edge is not asserted to
produce a pivot; the conclusions may instead use measured pivot rows.

There is a reversed version at the output. If \(b_s\ne0\) and the
same adjacent property holds along the final \(t\) edges, there
are actual rows \(\lambda_r\in\mathcal R_r\) supported in
\([1,s-r]\) with \((\lambda_r)_{s-r}\ne0\), \(0\le r\le t\).
Start with \(b^T\) and apply on the right one of
\(A-A_{ii}I,C-c_iI\) at the current last nonzero position \(i\).
The formulas at \(i-1\) are the same with edge \(A_{i,i-1}\), and
both expressions kill all positions at least \(i\).
Even without this property, the ordinary Newton rows
\[
        b^T\prod_{j=s-r+1}^s(A-A_{jj}I)\in\mathcal R_r
\]
always have support in \([1,s-r]\); only the nonzero terminal
coefficient is then not guaranteed. For common diagonal and nonzero
adjacent edges these Newton rows are the usual strict reverse pivots.
Inactive suffix deletion, if desired, is legitimate before defining
the physical stage count here, since no earlier row depends on it.

## 2. Asymmetric deformed-Hilbert budget for joint zero sites

Fix an integer \(0\le t\le p-1\) (with \(t\le s-1\) when testing literal terminal pivots), set
\[
  q=\lfloor(p-1-t)/2\rfloor,\qquad
  \epsilon=p-1-t-2q\in\{0,1\},\qquad Q=q+\epsilon.
\]
Take a set \(M\) of independent row evaluations on \(Z_q\), contained
in \([1,s-t]\), and a set \(M'\) of independent row evaluations on
\(Z_Q\). Write \(E=|M\setminus J_t|\) and
\(L=|[1,s]\setminus(M'\cup J_t)|\). Then
\[
                     E-L\ \ge\ (q+1)+|M|+|M'|-s.             \tag{2}
\]
For the leading pivot blocks just proved,
\(M=[f,f+q-a_0]\), \(M'=[f,f+Q-a_0]\) (assume they fit and
\(q\ge a_0\)). In that case
\[
                     E-L\ \ge\ q-2a_0+2-t-k.                \tag{3}
\]

Proof: choose one \(\omega\in\mathcal R_t\) nonzero on the whole
union \(J_t\), with nonsingular Gram for \(1,c,\ldots,c^q\).
To do this use scalar parameters in a row spanning family including
\(b^T\). Each active coordinate is a nonzero linear polynomial,
and the Gram determinant is nonzero at \(b^T\) by the exact rational
Hilbert Gram \(1/(i+j+1)\), \(0\le i,j\le q\).
Their product is nonzero and can be avoided over the infinite field.
This is just an auxiliary signed pairing, not a change of tableau.

On \(J_t\), \(\omega\) is a nondegenerate diagonal form.
Write \(D_h=Z_h|_{J_t}\) and let \(U\) be the \(q+1\) power probes.
Equation (1) gives \(D_Q\perp U+D_q\), since \(Q+q+t=p-1\).
Also \(U\cap D_q=0\) by the nonsingular Gram and orthogonality.
So \(|J_t|\ge q+1+\dim D_q+\dim D_Q\).
Their dimensions are bounded below by the active parts of \(M,M'\).
Cancel the number of inactive elements of \(M'\) from both sides
and obtain (2). Using unequal defect grades when \(\epsilon=1\)
keeps the last paid pivot; discarding it loses one guaranteed hole.

## 3. Fibre payment turns the holes into directional constraints

Let \(0\le r\le t\), \(\lambda\in\mathcal R_r\) be any row physically
supported in \([1,s-r]\), and let \(m_\lambda\) be the number of
distinct clock labels on its actual nonzero support.
Every \(z\in Z_a\) has **zero weighted total in each clock fibre**
whenever
\[
                         a+r+m_\lambda\le p.                 \tag{4}
\]
For each active label use its Lagrange selector on the
\(m_\lambda\) values; its leaf degree is at most \(m_\lambda-1\),
so (1) gives the assertion. The empty support case is vacuous.
In particular this uses only actual labels that contribute to the tap.
All \(E\) holes of (2) lie in its prefix; hence
\(m_\lambda\le s-r-E\) and \(a\le E-k\) suffices simultaneously
for all the taps. Their narrower support or repeated clocks can only
improve the literal test (4). Without the physical shrinkage the same
argument applies to every row in the full context flag, with the
more conservative grade \(a\le E-k-t\).

There are three different physical consequences.

* **Later same-clock partner.** If stage \(i\) is visible to this tap
  and some \(z\in Z_a\) has its first nonzero coordinate at \(i\),
  there must be another visible stage strictly later than \(i\) at
  the same clock. Otherwise the isolated fibre total of that \(z\)
  is \(\lambda_i z_i\ne0\); earlier same-clock stages cannot rescue
  it. This applies to all the paid leading pivots, including at the
  initial stages. In a globally clock-injective tableau those pivots
  are jointly invisible to every tested tap.
* **Terminal exact stage order.** If stage \(i\) is visible and its
  clock is unique on this tap, all members of \(Z_a\) vanish at \(i\),
  or equivalently its exact stage tree values hold through grade \(a\).
  The literal terminal pivots above therefore test the last \(t+1\)
  physical rows. In particular a nonzero clock \(c_i\) gives a local
  quadrature exact through degree \(a-1\): scale nodes \(c_j/c_i\)
  and weights \(A_{ij}/c_i\), and pool repeated nodes. At least
  \(\lceil a/2\rceil\) distinct nodes with nonzero pooled weight are needed,
  by the Hilbert Gram rank. If node \(1\) has nonzero pooled weight,
  at least \(\lfloor a/2\rfloor+1\) nodes are needed. Indeed with
  \(m\) nodes including \(1\), exactness through \(2m-1\) would
  make the monic product of the other \(m-1\) factors orthogonal
  to every degree-\((m-1)\) probe for the rational positive
  beta Gram with density \(1-X\), which is nonsingular over \(K\).
  Same-clock earlier donors can cancel the diagonal pool, so
  a nonzero physical diagonal alone is not that extra hypothesis.
* **Clock-fibre signed packing.** If (4) pays total grade \(a+a'\)
  with \(a\le a'\), products \(Z_a\odot Z_{a'}\) have zero
  fibre total as well. In a fibre \(F\) of the actual tap support
  let \(d_h^F=\dim(Z_h|_F)\) and \(M_F=\sum_{i\in F}\lambda_i\).
  The same diagonal-form dimension argument, with the constant
  probe when \(M_F\ne0\), yields
  \[
          |F|\ge d_a^F+d_{a'}^F+\mathbf 1_{M_F\ne0}.
  \]
  For \(a=a'=2\), a two-site fibre carrying a nonzero defect must
  have zero total weight, with the same defect values at both
  stages (its two weights are nonzero and opposite).
  For \(b^T\) there are at least \(\lceil p/2\rceil\) nonzero
  pooled clock masses by the exact Hilbert Gram, so summing gives
  \[
          |\operatorname{supp}b|
            \ge \lceil p/2\rceil+\sum_F(d_a^F+d_{a'}^F).
  \]
  This can be stricter than counting only the global defect rank:
  separate physical clock fibres occupy disjoint columns.
  No positivity of the actual weights is used.

A distinct interpretation of a jointly hidden column \(i\notin J_t\)
is available already when \(t\ge1\). The contexts \(b^TC^j A\),
\(0\le j<t\), give
\(\sum_{\ell>i} b_\ell c_\ell^j A_{\ell i}=0\); \(b_i=0\) kills
its diagonal term. Therefore either all pooled outgoing receiver
masses \(\sum_{\ell>i:\,c_\ell=\xi} b_\ell A_{\ell i}\) vanish, or
at least \(t+1\) distinct receiver labels have nonzero pooled weight.
In particular a single contributing active edge to the output support
cannot observe this column; actual same-clock cancellation is not ruled
out.

## 4. Uniform usable grades through p=20

Under the stated pivot block, the guaranteed grade from (3) and (4)
is
\[
             a_* = q-2a_0+2-t-2k.
\]
Thus target grade \(a\) is paid if
\(p\ge 2a+4a_0-3+3t+4k\) and the pivot block fits.
This is a sufficient threshold from this estimate, not a converse.
For \(s=p+1\), seed grade \(a_0=2\), the consequences in the
requested range follow without enumerating any tableau:

| Last tap degree \(t\) | Grade two for every tested tap | Grade four for every tested tap |
|---|---:|---:|
| 0 | \(p\ge13\) | \(p\ge17\) |
| 1 | \(p\ge16\) | \(p\ge20\) |
| 2 | \(p\ge19\) | beyond 20 by this estimate |

At grade two one gets later partners and singleton stage-order
constraints. At grade four one additionally gets the literal squared
branch compatibility in each fibre; the zero-mass two-site conclusion
does not follow from merely knowing the linear defect moments in a
small window. This statement uses neither long arithmetic clock runs
nor unreduced stability data. Outside the stated pivot regime, (2)
and (4) remain available on measured independent rows and actual
supports; a common-diagonal cyclic chart is one instance, not a
hidden assumption of the field-linear argument.
