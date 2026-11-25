# Exact rational five-stage strict SDIRK normal form at order five

For an arbitrary rational five-stage tableau of this type, the paid
forward and weighted-dual defects force D(1) and one shared quadratic
defect line. This reduces construction and validation to scalar
quadrature and four specified defect values followed by a unique
linear triangular solve. It does not require five distinct clocks.
The repeated-clock branch produces a
[five-stage rational witness](order-five-five-stage-repeated-clock.md).

## The exact forward and reverse criterion

Write \(\mathbf c\coloneqq A\mathbf 1\),
\(\mathbf y\coloneqq\mathbf 1-\mathbf c\),
\(C\coloneqq\operatorname{diag}(\mathbf c)\), and
\(W\coloneqq\operatorname{diag}(\mathbf b)\). For a genuinely
five-stage rational order-five tableau, all \(b_i\ne0\) by the
[quadratic-defect boundary](order-five-five-stage-necessary.md).
Define the physical weighted form and adjoint by
\[
\langle\mathbf v,\mathbf w\rangle_b
  \coloneqq \mathbf b\cdot(\mathbf v\odot\mathbf w),\qquad
A^\star\coloneqq W^{-1}A^\mathsf{T}W.
\]
The ordinary and reflected quadratic defects are
\[
\mathbf q\coloneqq A\mathbf c-\mathbf c^{\odot2}/2,\qquad
\overline{\mathbf q}\coloneqq A^\star\mathbf y-\mathbf y^{\odot2}/2.
\]
Define \(U\coloneqq\operatorname{span}_{\mathbb Q}
(\mathbf1,\mathbf c,\mathbf c^{\odot2})\).

**Criterion.** For a five-stage rational lower triangular matrix with
common nonzero diagonal and every output weight nonzero, order at least
five is equivalent to the following:
1. \(B(5)\): \(\mathbf b\cdot\mathbf c^{\odot j}=1/(j+1)\) for
   \(0\le j\le4\).
2. \(\mathbf q\perp U\) and \(\langle\mathbf q,\mathbf q\rangle_b=0\).
3. \(D(1)\): \(A^\star\mathbf1=\mathbf y\).
4. \(\overline{\mathbf q}=\lambda\mathbf q\) for some
   \(\lambda\in\mathbb Q\).

In the criterion \(\lambda\ne0\) automatically, and the first two
clocks are distinct, as are the final two. The five clock values as
a whole may have a repetition.

### The full order-five residual list

Use the literal reviewed tree stage weights \(\boldsymbol\Phi_t(A)\)
and order condition \(t!\,\mathbf b\cdot\boldsymbol\Phi_t(A)=1\).
Beyond \(B(5)\), the other 12 equations can be written as follows:
\[
\begin{aligned}
\mathbf q &\perp U,& \langle\mathbf q,\mathbf q\rangle_b&=0,\\
\mathbf r&\perp\operatorname{span}(\mathbf1,\mathbf c),&
\mathbf s&\perp\operatorname{span}(\mathbf1,\mathbf c),\\
\langle\mathbf1,A\mathbf c^{\odot3}\rangle_b&=1/20,&
\langle\mathbf1,AC\mathbf q\rangle_b&=0,\\
\langle\mathbf1,A\mathbf r\rangle_b&=0,&
\langle\mathbf1,A\mathbf s\rangle_b&=0,
\end{aligned}
\]
where
\[
\mathbf r\coloneqq A\mathbf c^{\odot2}-\mathbf c^{\odot3}/3,
\qquad \mathbf s\coloneqq A\mathbf q.
\]
For example, the original scalar moments paired with \(\mathbf1\)
are:

| Stage vector | Target |
|---|---:|
| \(A\mathbf c\), \(C A\mathbf c\), \(C^2 A\mathbf c\) | \(1/6,\ 1/8,\ 1/10\) |
| \((A\mathbf c)^{\odot2}\) | \(1/20\) |
| \(A\mathbf c^{\odot2}\), \(C A\mathbf c^{\odot2}\) | \(1/12,\ 1/15\) |
| \(A^2\mathbf c\), \(C A^2\mathbf c\) | \(1/24,\ 1/30\) |
| \(A\mathbf c^{\odot3}\), \(A C A\mathbf c\) | \(1/20,\ 1/40\) |
| \(A^2\mathbf c^{\odot2}\), \(A^3\mathbf c\) | \(1/60,\ 1/120\) |

Each entry is the one-branch or multibranch tree given by the displayed
products and matrix applications; there are \(1,1,2,4,9\) unordered
trees in successive orders. Subtracting the indicated pure powers
and replacing \(A^2\mathbf c\) by
\(\mathbf s+A\mathbf c^{\odot2}/2\) yields the residual list.
Conversely the same triangular substitutions recover every listed
moment, including \((A\mathbf c)^{\odot2}\).

### Why D(1) is forced, even with a repeated clock

Define \(\mathbf d\coloneqq A^\star\mathbf1-\mathbf y\).
The paid list gives
\[
\mathbf d\perp
(\mathbf1,\mathbf c,\mathbf c^{\odot2},\mathbf c^{\odot3},
\mathbf q,C\mathbf q).
\]
For the four pure powers, use
\(\langle\mathbf1,A\mathbf c^{\odot j}\rangle_b
=1/((j+1)(j+2))=\langle\mathbf y,\mathbf c^{\odot j}\rangle_b\).
The last two follow from the \(\mathbf s\) and \(AC\mathbf q\)
tests, since \(\mathbf y,C\mathbf y\in U\).

The Hilbert pairing on \(U\) has determinant \(1/2160\); its
orthogonal complement is nondegenerate of dimension two.
The nonzero isotropic vector \(\mathbf q\) belongs to the complement
and its orthogonal subspace there is just \(\mathbb Q\mathbf q\).
Here \(\mathbf q\ne0\) follows from the first entry
\(q_1=\gamma^2/2\). Thus \(\mathbf d=\kappa\mathbf q\).
If \(\kappa\ne0\), then \(\mathbf q\perp\mathbf c^{\odot3}\) and
\(\mathbf q\perp C\mathbf q\). Multiplication by \(C\) is self-adjoint
for the weighted form. These equations make \(C\mathbf q\perp U\)
and \(C\mathbf q\perp\mathbf q\), so \(C\mathbf q\in\mathbb Q\mathbf q\).

Consequently every nonzero entry of \(\mathbf q\) is at a single
clock. The [four-site rational quadrature requirement](order-five.md)
means that each clock class contains at most two physical rows and
has nonzero aggregate weight, because only five rows are available.
On a singleton, \(\mathbf q\perp\mathbf1\) already forces zero. On
two rows \(i,j\), that same condition yields
\(q_j=-b_iq_i/b_j\); the square norm on this class is
\(b_i(b_i+b_j)q_i^2/b_j\), nonzero for any nonzero \(q_i\).
This contradicts isotropy. Therefore \(\mathbf d=0\).

### Why the reflected defect shares exactly the same line

From \(D(1)\) the last physical clock is \(c_5=1-\gamma\), since the
last row of \(A^\star\) contains only its diagonal. In the identity
\[
\langle\overline{\mathbf q},\mathbf c^{\odot j}\rangle_b
=\langle\mathbf y,A\mathbf c^{\odot j}\rangle_b
 -\tfrac12\langle\mathbf y^{\odot2},\mathbf c^{\odot j}\rangle_b
\]
for \(j=0,1,2\), replace \(A\mathbf c^{\odot j}\) by
\(\mathbf c^{\odot(j+1)}/(j+1)\). The replacement costs only the paid
\(\mathbf q,\mathbf r\) pairings with \(\mathbf y\).
The remaining terms cancel by exact quadrature: the polynomial formal
integrals of \(y x^{j+1}/(j+1)\) and \(y^2 x^j/2\) are equal on
\([0,1]\). Also
\[
\langle\overline{\mathbf q},\mathbf q\rangle_b
=\langle\mathbf y,\mathbf s\rangle_b
 -\tfrac12\langle\mathbf y^{\odot2},\mathbf q\rangle_b=0.
\]
Thus \(\overline{\mathbf q}\in\mathbb Q\mathbf q\). Its last coordinate
is \(\gamma^2/2\ne0\), so the multiple \(\lambda\) is nonzero.

For sufficiency, conditions 3 and 4 imply
\[
A^\star\mathbf c=(\mathbf1-\mathbf c^{\odot2})/2-\lambda\mathbf q.
\]
Consequently
\(\langle\mathbf1,\mathbf r\rangle_b
=\langle\mathbf c,\mathbf r\rangle_b=0\): use respectively
\(A^\star\mathbf1=\mathbf y\) and the displayed identity, the paid
moments through degree four, and \(\mathbf q\perp U\).
The same two pairings for \(\mathbf s=A\mathbf q\) are zero because
\(\mathbf q\perp U\) and \(\langle\mathbf q,\mathbf q\rangle_b=0\).
The four remaining residual tests reduce under \(D(1)\) to
\(\langle\mathbf y,\mathbf c^{\odot3}\rangle_b=1/20\),
\(\langle\mathbf y,C\mathbf q\rangle_b=0\),
\(\langle\mathbf y,\mathbf r\rangle_b=0\), and
\(\langle\mathbf y,\mathbf s\rangle_b=0\). This recovers all 17 trees.

### The two end pairs must be distinct

If \(c_1=c_2\), then both equal \(\gamma\) and the second off-diagonal
entry \(a_{21}=0\). The first two rows each use their own stage only,
with the same scalar. Their stage weights agree for every rooted tree
by the reviewed recursion. Keep one row, sum the two incoming
coefficients in every later row, and sum the two output weights.
Induction on the tree shows the same remaining stage and output
weights. This gives a rational order-five four-stage strict SDIRK,
contradicting the established lower bound.

Reflect the chronological order of \(A^\star\), \(\mathbf b\) and
\(\mathbf y\). It is again lower triangular with the same common
diagonal. Its quadrature follows by replacing \(x\) by \(1-x\), its
forward defect is the reflected \(\lambda\mathbf q\), and its own
weighted adjoint has quadratic defect \(\mathbf q\). It therefore
passes the sufficient criterion just proved. Applying the identical
two-row fold to its first pair proves \(c_4\ne c_5\) for the original
tableau. This uses only the order-five criterion, not a general
weighted reflection theorem.

## Unique constructive solve from scalar data

Choose rational \(\gamma\ne0\), five clocks with
\(c_1=\gamma,\ c_5=1-\gamma,\ c_1\ne c_2,\ c_4\ne c_5\), and nonzero
weights satisfying \(B(5)\). Choose a scalar \(\lambda\ne0\) and
a vector \(\mathbf q\perp U\) with
\(\langle\mathbf q,\mathbf q\rangle_b=0\), such that
\[
\begin{aligned}
q_1&=\gamma^2/2,&
q_2&=2\gamma c_2-\gamma^2-c_2^2/2,\\
\lambda q_5&=\gamma^2/2,&
\lambda q_4&=2\gamma y_4-\gamma^2-y_4^2/2 .
\end{aligned}
\]
There is exactly one order-five tableau having these data. To
construct it let \(S\coloneqq W(A-\gamma I)\), strictly lower
triangular, and set the desired row and column totals
\[
\begin{aligned}
\ell_i&\coloneqq b_i(c_i-\gamma),&
\rho_i&\coloneqq b_i(c_i^2/2+q_i-\gamma c_i),\\
\upsilon_j&\coloneqq b_j(y_j-\gamma),&
\nu_j&\coloneqq b_j((1-c_j^2)/2-\lambda q_j-\gamma c_j).
\end{aligned}
\]
The two row moments are \((\ell_i,\rho_i)\) with multipliers
\((1,c_j)\). The two column moments are \((\upsilon_j,\nu_j)\) with
multipliers \((1,c_i)\). The four boundary equations make row 1 and
column 5 zero, \(\rho_2=c_1\ell_2\), and \(\nu_4=c_5\upsilon_4\).

Assign \(S_{21}=\ell_2\) and \(S_{54}=\upsilon_4\).
Column 3 uses two rows 4 and 5; solve for \(S_{43},S_{53}\)
via its moment pair since \(c_4\ne c_5\). Then in each of rows
3, 4, 5 solve for its first two entries after subtracting
already-assigned terms. This uses \(c_1\ne c_2\).
These steps fix all ten strict lower entries.

The final column tests at 1 and 2 hold automatically. In fact \(B(5)\)
and the two lowest pairings of \(\mathbf q\) give the exact
compatibilities
\[
\sum_i\ell_i=\sum_j\upsilon_j,\qquad
\sum_i\rho_i=\sum_jc_j\upsilon_j,\qquad
\sum_i c_i\ell_i=\sum_j\nu_j,\qquad
\sum_i c_i\rho_i=\sum_j c_j\nu_j .
\]
In each untested column-pair residual these identities force its
sum and \(c_j\)-weighted sum to vanish; distinct \(c_1,c_2\)
force each residual zero. Finally set \(A=\gamma I+W^{-1}S\)
and apply the sufficient criterion. Conversely every genuine
rational five-stage order-five tableau supplies this data,
by the necessary statements above. No comparison between the
interior clocks and the end clocks beyond the specified two pairs is
needed for this solve.
