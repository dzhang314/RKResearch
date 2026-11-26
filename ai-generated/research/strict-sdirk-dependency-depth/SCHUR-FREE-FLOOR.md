# A Schur-free replacement at the seven-clock floor

**Pure mathematical proof.** Let a triangular RK tableau over a
nontrivial commutative ring have actual common diagonal \(\gamma\) and
satisfy the literal rooted order equations through \(p\ge15\).
Then its physical stage count satisfies
\[
                              s\ge p+1 .
\]
No signs, ordered field, stability, nonvanishing diagonal, or resultant
premise is required. This is a replacement for the two Schur-dependent
steps of the characteristic-zero synthesis, not a reduction of Schur.
It does not concern the surplus-stage case \(s=p+1\), differing diagonals,
or exact-order searches.

By reviewed coefficient mapping to a maximal residue field, it is
enough to prove the result over fields with the paid integer units.
All such fields have characteristic zero or prime greater than \(p\).
In the proof below the bounded word model and the rectangle and
arithmetic identities are used in the characteristic-safe form of the
companion CHARACTERISTIC-TRANSFER.md.

Write \(B=A-\gamma I\), \(\mathbf c=A\mathbf 1\),
\(\lambda_j=\mathbf b\cdot B^j\mathbf 1\) for \(j+1\le p\).
If \(\gamma=0\), the tall bound and explicit equality rectangle give
the result already for \(p\ge5\). Hence suppose \(\gamma\ne0\) and
\(s\le p\). The paid consecutive tall recurrence excludes \(s\le p-2\)
by strict nilpotence. Only \(s=p-1\) and \(s=p\) remain.

## 1. Saturation \(s=p-1\): the six-clock remainder is generic

Here \(s\ge14\), \(\lambda_s=0\), and
\(L\coloneqq\lambda_{s-1}\ne0\) by the consecutive-zero argument.
The cyclic rectangle needs only order through \(s\), which is paid.
In its nondegenerate chart it forces global nonzero-step arithmetic
clocks. In its degenerate chart it forces either an arithmetic prefix
through \(s-2\), or two equal-step runs with lengths summing to \(s-2\).
The step is nonzero. A run of seven is impossible by the local proof.
If neither split run contains seven, their lengths are both six, since
their sum is at least twelve. In particular the first run begins at
physical stage 1 and its step equals \(x_2=c_2-\gamma\).

Use the **branching calculation before Schur** in the saturation
proof, at the actually paid order \(s+1\). It gives the cubic constraint
\[
 C_s(t)=0,\qquad C_s(t)=(s+1)t^3-4s t^2+2(s-3)t+4,
 \qquad t=x_2/\gamma .
\]
All the denominators in that calculation are paid integers and the
nonzero \(L,\gamma\). In the split chart this \(t\) is exactly the
normalized run step. It is not \(2/3\): the cubic evaluates there to
\(4(2-s)/27\ne0\), since \(2,3,s-2\) are units.

For clarity, here is the exact six-clock use of the degenerate chart.
Use reverse moments \(m_k=\gamma^k\lambda_{s-1-k}/L\),
\(\mu(y^k)=m_k\). Put
\[
 {\cal D}=m_2-m_1^2,\qquad
 {\cal U}=m_1m_2-m_3,\qquad
 {\cal V}=m_4-m_2^2 .
\]
The rectangle identities \(E=-2\gamma D+\gamma^2 U\) and
\(\Delta=\gamma^4(DV-U^2)=0\), with \(D\ne0\) and the actual step
\(-E/D\), give
\[
 {\cal D}\ne0,\qquad {\cal D}{\cal V}={\cal U}^2,\qquad
                      2-t={\cal U}/{\cal D}.
\]
Consequently \(g(y)=F_1(y)-\mu(F_1)\), monic quadratic, satisfies
\[
 \mu(g)=0,\quad
 \mu(gy)=-{\cal U}+(2-t){\cal D}=0,\quad
 \mu(gy^2)={\cal V}-(2-t){\cal U}=0 .
\]
Mark gaps of counts 1 and 2 inside the six consecutive clocks. There
are three holes and two marked links, so the occupied-slot window
spans at most \(3+2+1=6\) clocks. The standard single and double
calibrations therefore give \(\mu(F_1F_2)=\mu(F_1)\mu(F_2)\).
Thus \(\mu(gF_2)=0\). Since \(F_2\) has cubic coefficient
\(1-3t/2\ne0\), the three preceding zero moments give \(\mu(gy^3)=0\).
These four relations give a fixed monic quadratic recurrence on
\(m_0,\ldots,m_5\). The paid reverse-tall rows are
\[
 (s-k)m_k=(\xi-2(s-1-k))m_{k+1}-(s-2-k)m_{k+2},
                   \qquad \xi=\gamma^{-1},\quad 0\le k\le3 .
\]
The fixed-recurrence rejection in the arithmetic proof uses exactly
these four rows. Indeed one may extend the quadratic recurrence and
factor it over an algebraic closure. On a geometric mode \(r^k\) the
reverse-tall residual is \(r^k\) times an affine function with slope
\(-(1+r)^2\), and that function equals \(\xi\) at \(r=-1\). Two
distinct nonzero modes have residual in a monic order-four recurrence;
four zeros kill that residual, and the two exponential-affine
components are independent. For a repeated nonzero root the divided
residual is quadratic in \(k\); its first three zeros suffice. If
\(r\ne-1\), its quadratic and then linear coefficients kill both mode
coefficients. If \(r=-1\), its linear and then constant coefficients
do so using \(\xi\ne0\). With a zero root, rows at \(k=1,2\) kill the
remaining nonzero mode if any; row \(1\) forces \(m_1=0\) if both roots
are zero. Then row \(0\) contradicts \(m_0=1\). Thus saturation is
impossible, without comparing the cubic with the Laguerre polynomial.

## 2. Equality \(s=p\), cyclic branch

If \(L\coloneqq\lambda_{s-1}\ne0\), the usual rectangle gives an
arithmetic run of seven: the nondegenerate chart is globally
arithmetic, an unsplit prefix is long enough, and in the split
case the lengths sum to \(s-2\ge13\). All steps are nonzero.
The local arithmetic argument excludes this branch over the paid field.

## 3. Equality \(s=p\), missed longest chain: one compulsory hole

Suppose \(L=0\). Write \(M\coloneqq\lambda_{s-2}\ne0\), again by
the consecutive-zero recurrence. If \(b_s=0\), strict lower
triangularity ensures that none of the first \(s-1\) rows of \(A\)
uses its final column. By structural induction their rooted stage
values are unchanged on deleting that row and column, and the deleted
stage did not enter the scalar output. That would be the saturation case
of Section 1, already disproved. Hence \(b_s\ne0\) and some adjacent
entry \(B_{i,i-1}\) vanishes.

A nonzero strict path must omit at least one of the pair
\(\{i-1,i\}\), since retaining both would traverse that zero edge.
In particular the one-hole paths have possible nonzero weights only
at these two holes, and the sum of those weights is \(M\).
The already paid one-hole clock law with \(L=0\), using its partial
weight zero before the pair and \(M\) after the pair, gives
\[
 \begin{aligned}
 c_j&=\gamma+(j-1)\epsilon &&(1\le j\le i-2),\\
 c_j&=\gamma+(j-2)\epsilon &&(i+1\le j\le s),
 \end{aligned}
 \qquad \epsilon=\kappa/M .
\]
The two runs outside the pair have total length \(s-2\ge13\),
so one has seven consecutive physical sites.

The common step \(\epsilon\) cannot vanish. If it did, those seven
clocks would all be \(\gamma\). On a two-hole path the physical
index in occupied slot \(k\) is between \(k\) and \(k+2\).
If the constant run contains \([r,r+6]\), use occupied slots \(r+1\)
and \(r+2\). Both windows lie inside the run. Both shifted-clock readings
at strict length \(N=s-3\) are then zero. Their paid formal values,
at \(a=k-1\) and \(a+1\), are
\[
  M+a\eta,\quad M+(a+1)\eta,\qquad
  \eta=\ell(J^2T^{N-1}1).
\]
Indeed \(T^{N-a}(X-\gamma)T^a1=T^{N+1}1+aJ^2T^{N-1}1\).
Subtracting the two equations gives \(\eta=0\) and \(M=0\),
contradiction. Thus the chosen seven-run has nonzero step.

### Compulsory-hole placement in the seven-run

Set effective size \(m=s-1\), top value \(M=\lambda_{m-1}\),
and use \(m-h\) occupied sites for \(h\) desired additional
internal omissions. There are \(h+1\) physical holes. Let
\([r,r+6]\) be the chosen run outside the pair. For positive
target counts \(d_1,\ldots,d_q\) with \(h=\sum d_j\) and
\(h+q\le6\), take consecutive occupied links as follows.

- **Prefix run, \(r+6\le i-2\):** start the first link at
  occupied slot \(r\). Every relevant endpoint slot \(\nu\)
  has physical index \(v_\nu\le\nu+h+1\le i-1\). On a
  nonzero path a required pair hole is strictly after
  \(v_\nu\): if \(v_\nu=i-1\), that stage is retained, so
  the hole is \(i\); if \(v_\nu<i-1\), both pair indices
  are later. Thus \(v_\nu\le\nu+h\) after all. All actual
  marked endpoints lie in \([r,r+q+h]\).
- **Tail run, \(r\ge i+1\):** start at occupied slot
  \(r-1\). Every relevant endpoint slot \(\nu\) has
  \(v_\nu\ge\nu\ge i\), so a required pair hole has
  already passed. This is also true for \(v_\nu=i\),
  since then \(i\) is retained. Hence
  \(\nu+1\le v_\nu\le\nu+h+1\), putting all endpoints in
  the same \([r,r+q+h]\).

Both occupy valid slots: in the prefix case
\(r+q+h\le i-2\le s-2\), and in the tail case
\(r+q+h\le s\). Thus the last marked slot is at most \(m-h\).
The reasoning applies to every candidate path of nonzero weight,
not just to paths after passing a mark.

Use the original degree-\(d_j\) mark
\(\prod_{a=1}^{d_j}(w-a\epsilon)\) on each link.
A surviving mark with endpoints in the run has at least \(d_j\)
holes in that link; at exactly \(d_j\) its value is
\(\epsilon^{d_j}d_j!\ne0\). Because the marked intervals lie
outside the compulsory pair and there are only \(h+1\) holes,
survival forces exactly one pair hole, exactly \(d_j\) at each
mark, and no others. For each possible omitted pair index,
there is one retained list. The actual skipped physical intervals
are the same on both lists: their donor indices are
\(r+j-1+\sum_{t<j}d_t\), with the one passed pair hole compensated
by the tail slot shift.

### The same calibrated skips in the two base paths

Both one-hole base lists retain the entire chosen run. At least
one has nonzero weight because their sum is \(M\ne0\), so all
adjacent factors *inside that run* are nonzero. For any selected
skip divide its actual entry by the product of its own adjacent
block in the run, defining \(\theta_{u,v}\). No outside
adjacency or individual base-path weight is divided by.

The marked lists come from each one-hole base list by exactly
these same disjoint edge-block replacements. Their total weight is
\(M\prod\theta_{u,v}\), including the case when either base
weight or a skip is zero. To calibrate each specific skip separately,
put one mark on occupied link \(u\) to \(u+1\) for a prefix skip
or \(u-1\) to \(u\) for a tail skip, with \(h=d_j=v-u-1\).
The same prefix or tail bound above puts every marked endpoint
of a nonzero path inside \([u,v]\). Survival forces the exact skip,
and gives the single-mark output \(\epsilon^{d_j}d_j!\,M\theta_{u,v}\).

Now every marked word uses \(m-1-h\) strict hops, \(h\) clock
degrees, and its initial leaf, for total paid order exactly \(m=s-1\).
The published formal polynomials \(F_d\) apply with
\(t=\epsilon/\gamma\) and
\(\mu(y^k)=\gamma^k\lambda_{m-1-k}/M\).
The same single-mark normalization gives
\(\mu(F_d)=\epsilon^d\theta_{u,v}\). The combined word gives
\[
              \mu\!\left(\prod_jF_{d_j}\right)
                       =\prod_j\mu(F_{d_j})
                   \qquad(h+q\le6).
\]
Only \(M\), the actual adjacent block in the run, and paid
factorials were used to normalize. The reverse tall recurrence
is the same with size \(m\), and \(m_0=1\). The arithmetic
contradiction using marks with \(h+q\le6\) therefore eliminates this missed-chain
case as well. The original late-break/early-break Schur split is
not needed.

This uses strictly the \(s=p\) broken-pair geometry, with the
shorter paid order \(s-1\) for the local masks. It is not a
surplus-stage isolation assertion.

## 4. Return to commutative rings

The literal tree equations map to a maximal residue field,
preserving the physical number of stages and the common-diagonal
condition. The field proof covers both its zero and nonzero
diagonal. This proves the claimed floor over all nontrivial
commutative rings. In particular it does not infer invertibility
from nonzeroness of a ring pivot. No Lean body, runner, repository
operation, or specific tableau search was performed.

The [split-run proof](../../lower-bounds/sdirk-paid-split-floor.md) lowers the threshold of this ring result to order eleven.
