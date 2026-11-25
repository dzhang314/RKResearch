# Affine selector payment and a rank certificate for repeated RK clock fibres

Source-only proof against checked RKResearch main
`7d5ba756fcf30d2e970ec5579bb185079b83384b`.
No Lean execution, shared checkout edits, or new unconditional stage claim.

## 1. Affine payment at actual order 2n−2

Work over a characteristic-zero field. Use the actual `HasOrder p A b`,
physical clocks \(c=A\mathbf1\), and the reviewed symmetric bilinear form
\(S=\texttt{symplecticPair A b}\):

    S(f,g) = sum_i b_i [f_i (A g)_i + g_i (A f)_i] - (sum_i b_i f_i)(sum_j b_j g_j).

The public bridge in `ReviewedNative/NativeSymplecticPairing.lean` and
`ReviewedNative/GradedPrimitives.lean` gives \(S(F(c),G(c))=0\) whenever
\(\deg F+\deg G+2\le p\). No symplectic tableau assumption is made.

Let \(T\) be any set of \(n\ge2\) distinct labels, \(q_t=\prod_{u\in T\setminus\{t\}}(X-u)\)
the monic selector, \(k_t=q_t(t)\ne0\), and \(\sigma=\sum_{t\in T}t\).
The two leading terms are
\[
q_t=X^{n-1}+(t-\sigma)X^{n-2}+R_t,\qquad \deg R_t\le n-3
\]
(for \(n=2\), \(R_t=0\)). If \(p\ge2n-2\), every monomial pair in
\(S(q_u(c),q_v(c))\) is paid except possibly bidegrees
\((n-1,n-1),(n-1,n-2),(n-2,n-1)\). Consequently
\[
K_{uv}:=S(q_u(c),q_v(c))=\alpha+\beta(u+v-2\sigma),
\quad\alpha=S(c^{n-1},c^{n-1}),\quad
\beta=S(c^{n-2},c^{n-1}),
\]
where powers of stage vectors are componentwise.
The affine matrix has rank at most two, exactly two if \(\beta\ne0\);
on two distinct labels its \(2\)-square determinant is
\(-\beta^2(u-v)^2\). At \(p\ge2n-1\), \(\beta=0\); at \(p\ge2n\),
\(\alpha=\beta=0\). In particular \(K_{aa}-K_{zz}=2\beta(a-z)\)
and \(2K_{az}=K_{aa}+K_{zz}\).

For the main application a smaller proof suffices: every linear
combination of the \(q_t\)'s whose label coefficients sum to zero has
degree at most \(n-2\), by monicity. In particular
\[
q_a-q_z=(a-z)\!\prod_{x\in T\setminus\{a,z\}}(X-x)\quad(a\ne z).
\]
Thus for any matrices \(P,Q\) with zero-sum columns (also if supported
on a subset of the labels), \(P^{\mathsf T}KQ=0\). Each contrast gain is
one degree, so together they annihilate the affine matrix without
knowing its slope.

## 2. Retain the actual joint hidden correction

Write \(s_t=\mathbf1_{c=t}\), \(h_t=q_t(c)-k_t s_t\), and
\(B_t=\sum_{c_i=t} b_i\). The vector \(h_t\) is literally
`hiddenMask A T (visibleSelector T t)`, zero on \(T\) and not
assumed zero off it. Define
\[
M_{uv}=\sum_{c_i=u,c_j=v}b_iA_{ij},\qquad
D_{uv}=M_{uv}+M_{vu}-B_uB_v,\qquad \widetilde D_{uv}=k_u k_vD_{uv}.
\]
Bilinearity gives
\[
K=\widetilde D+L,\qquad
L_{uv}=k_u S(s_u,h_v)+k_v S(h_u,s_v)+S(h_u,h_v).
\]
Here \(L\) includes both cross-block terms and the hidden–hidden term.
Neither cover of aggregate output sites nor low rank of one component
certifies small rank of the whole sum. A diagonal correction vector
alone does not carry this information.

For actual lower triangular \(A\), put
\[
d_t=\sum_{c_i=t} b_iA_{ii},\quad
E_t=\sum_{i<j,\ c_i=c_j=t}b_jA_{ji},\quad
\delta_t=2k_t^2E_t,\quad b^0_t=k_t^2(2d_t-B_t^2).
\]
\(E_t\ne0\) forces an actual nonzero weighted strict edge, hence at
least two stages in the fibre. \(E_t=0\) does not prove it singleton.
For strict ERK, \(b^0_t=-(k_tB_t)^2\); for common diagonal \(\gamma\),
\(b^0_t=k_t^2B_t(2\gamma-B_t)\). Arbitrary DIRK uses actual \(d_t\).

Let \(D^0\) retain the actual off-diagonal entries of \(\widetilde D\)
and replace the diagonal by \(b^0_t\). Thus \(K=D^0+\operatorname{diag}\delta+L\).
For \(C=D^0+L\) the two-label mixed test gives
\[
\delta_a+\delta_z=2C_{az}-C_{aa}-C_{zz}.
\]
A nonzero right side forces a repeated fibre at \(a\) or \(z\).
For three distinct labels \(a,z,v\), the contrasts \(e_a-e_z,e_a-e_v\)
overlap only at \(a\), so
\[
\delta_a=C_{az}+C_{av}-C_{zv}-C_{aa}.
\]
A nonzero right side now forces the particular fibre \(a\). This is
equivalently \(K_{aa}=K_{az}+K_{av}-K_{zv}\).
For \(n=2\) the double contrast alone determines only the sum.

## 3. Rank and sign certificates

Fix any subset \(I\subseteq T\) of \(m\) labels; restrict to \(I\) before
applying the certificates. For any zero-sum contrast packets \(P,Q\),
\[
P^{\mathsf T}\operatorname{diag}(\delta)Q=-P^{\mathsf T}(D^0+L)Q.
\]
If \(r_\delta\) is the number of \(t\in I\) with \(E_t\ne0\), then
\[
r_\delta\ \ge\ \operatorname{rank}P^{\mathsf T}(D^0+L)Q
\ \ge\ \operatorname{rank}P^{\mathsf T}D^0Q-\operatorname{rank}P^{\mathsf T}LQ.
\]
Use rank of a product and subadditivity. This works with rectangular
packets and signed weights, with no further order cost compared with
the constant \(2n-1\) case. A weaker unprojected bound is
\(r_\delta\ge\operatorname{rank}D^0-\operatorname{rank}L-2\).
Known small rank of \(L\) can be used as a bound on any of its
compressions. Over an ordered field, with \(P=Q\), the positive and
negative counts of the \(E_t\)'s are respectively at least
\[
i_-(P^{\mathsf T}D^0P)-i_+(P^{\mathsf T}LP),\qquad
i_+(P^{\mathsf T}D^0P)-i_-(P^{\mathsf T}LP)
\]
clipped at zero, where \(i_\pm\) are maximal definite-subspace
dimensions. A definite subspace of one signed summand intersects the
other's same-sign semidefinite subspace in at least the stated
dimension. This remains true if \(P\) has a kernel.

A constant all-ones leakage block is killed by the contrast, but
constant diagonal entries alone are not enough. On \(I\) the full
contrast ignores precisely the symmetric matrices of the form
\(\mathbf1 v^{\mathsf T}+v\mathbf1^{\mathsf T}\). Indeed the anchored
\(e_i-e_a,e_j-e_a\) contrasts imply \(L_{ij}=L_{ia}+L_{aj}-L_{aa}\).
Take \(v_i=L_{ia}-L_{aa}/2\). These invisible blocks need not have
constant diagonal.

### Exact support classification with a reference completion

Let \(m\ge2\). Let \(H\) be any symmetric reference completion of the *actual scaled
off-diagonals* \(\widetilde D_{uv}\) on \(I\). Its selected diagonal need
not be \(b^0\). Let \(P\) have as columns a basis of \(\mathbf1^\perp\) on
\(I\), and put
\[
g_t=b^0_t+\delta_t-H_{tt},\qquad
r_*=\operatorname{rank}\!\big(P^{\mathsf T}(H+L)P\big).
\]
Exact contrast payment makes \(r_*=\operatorname{rank}(P^{\mathsf T}
\operatorname{diag}(g)P)\). There are just two cases:

* If some \(g_a=0\), use the anchored columns \(e_i-e_a\).
  The compression is diagonal with entries \(g_i\) for \(i\ne a\).
  Therefore \(r_*=\#\{t:g_t\ne0\}\).
* If all \(g_t\ne0\), the radical of the form on \(\mathbf1^\perp\)
  consists of \(z_t=\lambda/g_t\) with \(\sum_t z_t=0\): its product
  by \(\operatorname{diag}(g)\) must lie in the span of \(\mathbf1\).
  So \(r_*=m-1\) if \(\sum_t1/g_t\ne0\), and \(r_*=m-2\) otherwise.

Consequently if \(m\ge3\) and \(r_*\le m-3\), at least
\[
\boxed{\#\{t:b^0_t\ne H_{tt}\}-r_*}
\]
labels have \(E_t\ne0\), with negative lower bounds clipped at zero.
At most \(r_*\) of these gaps can have nonzero
\(g_t\); every remaining gap forces
\(\delta_t=H_{tt}-b^0_t\ne0\). An independently proved bound
\(\operatorname{rank}(P^{\mathsf T}HP)+\operatorname{rank}(P^{\mathsf T}LP)
\le r\le m-3\) gives the same result with \(r\). The extra information is
that the full-support alternative is excluded. There is no forced one-
or two-fibre loss merely from having used contrasts.

When \(r_*\in\{m-2,m-1\}\), rank alone leaves open full support;
use the general preceding rank bound or inspect actual mixed entries.
For \(m\ge3\) the full contrast matrix determines all \(g_t\): relative to
anchor \(a\), it is \(\operatorname{diag}(g_i:i\ne a)+g_a\mathbf1\mathbf1^{\mathsf T}\).
An off-diagonal entry gives \(g_a\), and subtraction from the diagonal
gives the other entries. For \(m=2\) it contains only \(g_1+g_2\).

Two useful independent off-diagonal premises:

* \(M_{uv}+M_{vu}=B_uB_v\) for all unequal \(u,v\) permits \(H=0\).
  Every live ERK label has a baseline gap, so a certified
  projected leakage rank \(r\le m-3\) forces at least \(m-r\) repeated
  live fibres. For DIRK/SDIRK count the labels with \(2d_t\ne B_t^2\).
* \(M_{uv}+M_{vu}=0\) for all unequal \(u,v\) permits
  \(H=-(kB)(kB)^{\mathsf T}\). Strict ERK has no baseline gaps and
  this gives no repeats. For nonzero common diagonal and live weights,
  every label is a gap (\(b^0_t-H_{tt}=2\gamma k_t^2B_t\)).
  The rank to certify is of the projected sum \(H+L\).

For \(m\) occupied labels, a bound of \(q\) repeated fibres gives
at least \(m+q\) stages on their union. It is not an unrestricted floor.

## 4. Actual general sharpness, not just matrix examples

The reviewed-source donor realization permits one active row per site
and pure hidden donors with clocks away from those sites. In its
Vandermonde right-hand sides one can also subtract the contributions
of prescribed strict links to earlier pure rows. The same induction
on actual trees proves purity, including the smaller-child action of
the same-row diagonal.

Use \(n\) Gaussian live sites over the real algebraic field and weights
\(B_t>0\), paying quadrature order \(2n\). Place the unweighted donor
bank off \(T\). For strict ERK the forced first clock is zero, already
off \(T\). For common positive diagonal choose sufficiently small
\(\gamma>0\) not in \(T\) with \(2\gamma<\min_t B_t\).
Arbitrary DIRK also permits this and can vary the active diagonals
within that range. Only final active rows have nonzero output.

**Rank alone is insufficient.** With no extra stage at a live label,
all its physical fibres are singleton. In ERK use no live-to-live links:
\(\widetilde D=-(kB)(kB)^{\mathsf T}\), so \(L=-\widetilde D\) has rank one
since full order makes \(K=0\). For positive common \(\gamma\) as above,
prescribe \(\widetilde D=-vv^{\mathsf T}\) with \(v_t=\sqrt{-b^0_t}\).
The forced diagonals agree. For each pair of distinct labels, prescribe
the one allowed strict edge (earlier to later active row) to obtain
the desired symmetric off-diagonal entry, and retune the hidden donor
Vandermonde equations. This yields another rank-one \(L\) with every live
physical fibre still singleton. Thus small rank of \(L\) alone cannot
force a single excess live stage. The construction says nothing about
unrelated hidden multiplicities.

**The off-diagonal-balanced \(n-r\) bound is attained.** For
\(0\le r\le n-3\), choose exactly \(n-r\) labels to repeat. Put one
pure zero-output tap of the prescribed clock before the active rows
for each chosen label, none for the others. Prescribe the strict
entry from any earlier active row \(u\) to a later active row \(v\)
to be \(B_u\), giving off-diagonal balance. Prescribe the incoming
same-clock tap at each chosen \(t\) by \(A_{t,\mathrm{tap}}=B_t/2-A_{tt}\).
It is a nonzero weighted strict edge and gives \(M_{tt}=B_t^2/2\).
The unchanged lower-triangular donor induction gives actual order
at least \(2n\). Now \(\widetilde D\) is diagonal on the \(r\)
unrepeated labels, so \(L=-\widetilde D\) has rank \(r\).
There are exactly \(n-r\) repeated live fibres.

For exact order \(p=2n-2\) with \(n\ge3\), perturb only the last
weighted row on \(p\) distinct pure hidden donors of the last bank.
Their barycentric weights annihilate powers through \(p-2\) and pair
to one with degree \(p-1\). All paid actual trees are unchanged by
child induction, since their donor profiles have degree at most
\(p-2\), and no other stage uses the changed row. The tree with one
child equal to the order-\(p\) bush changes by nonzero output; its
clock and literal child response \(c^{p-1}\) were unchanged.
The threshold order is thus exact. The physical \(T\)-block is fixed,
and \(K\) remains fixed because every selector has degree
\(n-1\le p-2\); hence \(L\) and the counts remain fixed. This verifies
both sharpness families without extrapolating from small test cases.

## 5. Minimal future Lean gate; not run

The first theorem can reuse the public `evalNodes_mem_treeSpace` and
`symplecticPair_zero_on_paid_tree_spaces`, and the previous source-only
selector factor difference. It needs only to assert that
`symplecticPair A b` vanishes on the two vectors
`evalNodes A (visibleSelector T a - visibleSelector T z)` and
`evalNodes A (visibleSelector T u - visibleSelector T v)` under
`2 * T.card ≤ p + 2`, the four endpoints in \(T\). If endpoints
coincide the corresponding vector is zero; otherwise each pays the
one-degree refund. Keep the mixed leakage split and the elementary
linear algebra as separate providers. The rank classification is about
a diagonal form on the zero-sum hyperplane and needs no RK definitions.
Use lower triangularity only for the final actual-edge client.

Optional extension: for \(p\ge2n-j\) the corrected matrix is a symmetric
polynomial in the two labels of total degree at most \(j-1\). Indeed
the coefficient of \(X^{n-1-d}\) in \(q_t\) is a monic degree-\(d\)
polynomial in \(t\) by synthetically dividing \(\prod_{x\in T}(X-x)\)
by \(X-t\); a remaining unpaid pair has sum of the leading-term
deficits less than \(j\). Thus left/right contrast packets annihilating
label moments of degrees less than \(r,s\) pay when \(r+s\ge j\).
This extension does not imply new bounds by itself.
