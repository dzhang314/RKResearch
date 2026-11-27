# The two order-ten DIRK cubic pivots cannot be adjacent

An eleven-stage lower triangular RK tableau of order ten has four zero
diagonals over any field: the first, the last, and interior indices $i<j$
with **$j-i\ge2$**. The proof uses the actual reviewed tree-order
predicate; it does not assume ordered coefficients, distinct clocks,
or individually nonzero output weights. Over every nontrivial
commutative ring, the same separation holds for four **nonunit**
diagonal entries by reduction to any residue field. This excludes the
adjacent branch, not the eleven-stage equality case.

## Mixed reads across the putative adjacent cut

The [crossed cubic argument](dirk-order10-crossed-cubic-pivots.md)
produces an actual forward grade-three column $\boldsymbol{v}$ vanishing before
row $i$, and a backward grade-three row $\boldsymbol{\lambda}$ vanishing after
row $j$. Both endpoint diagonals of this cut are zero. The corresponding
nonzero profiles have forms $P=x(a+bx+dx^2)$ and
$Q=(1-x)(h+\ell x+m x^2)$.

If $j=i+1$, the only tap in a mixed primitive read is
$a_{ji}\lambda_j v_i\ne0$. The literal Volterra commutator then shows
$c_i=c_j=\xi$ because $\boldsymbol{\lambda} A^2\boldsymbol{v}=0$ on the adjacent cut.
Every ordinary cross read has the form $\boldsymbol{\lambda} C^k \boldsymbol{v}=T\xi^k$,
and every single-primitive cross read has form
$\lambda C^k A C^qv=S\xi^{k+q}$, where $T=\lambda v$ and
$S=a_{ji}\lambda_j v_i$. The orders paid are $k\le3$ and $k+q\le2$,
respectively.

Write $L_k=I(Qx^kP)$ and $J_{q,k}=I(Qx^k J(x^qP))$, where $J$ is
integration from zero and $I$ integration from zero to one. The integer
system is obtained from these eight equations:
$$
\begin{gathered}
 L_{k+1}-\xi L_k=0\quad(k=0,1,2),\\
 J_{0,1}-\xi J_{0,0}=0,\quad J_{1,0}-J_{0,1}=0,\quad
 J_{0,2}-\xi J_{0,1}=0,\quad
 J_{1,1}-J_{0,2}=0,\quad J_{2,0}-J_{0,2}=0 .
\end{gathered}
$$
Its unknowns are the nine entries of the outer product
$(a,b,d)^\mathsf T(h,\ell,m)$, in row-major order. For the column
corresponding to $x^e(1-x)x^f$ ($e=1,2,3$ and $f=0,1,2$), the contribution
to $L_k$ is $B(e+f+k)$ and to $J_{q,k}$ is
$B(e+f+q+k+1)/(e+q+1)$, where $B(n)=1/((n+1)(n+2))$.
All probe denominators are paid through order ten. The row clearing
scales, in the displayed order, are
$$
 840,\ 2520,\ 2520,\ 10080,\ 10080,\ 30240,\ 151200,\ 30240.
$$
Their prime support is exactly $2,3,5,7$: the different factors are
$2^3 3\cdot5\cdot7$, $2^3 3^2\cdot5\cdot7$,
$2^5 3^2\cdot5\cdot7$, $2^5 3^3\cdot5\cdot7$, and
$2^5 3^3\cdot5^2\cdot7$.

## Scalar rank proof, including exceptional clocks

The signed maximal-minor vector of the cleared system is
$$
36\xi^2(\xi-1)^2(2\xi-1)
  (10,-35,28,-105,336,-252,196,-588,420).
$$
The constant vector is visibly in the kernel; away from
$0,1,1/2$, the minor at its first coordinate is nonzero, so it spans.
Its first $2\times2$ minor in the $3\times3$ product chart is $-315$,
which is a paid nonzero integer. No nonzero multiple has rank one.

At the exceptional clocks, the following integer pairs, written in the
same row-major order, span the kernels. For $1/2$, use twice the integer
matrix evaluated there. The first seven rows on the complement of the
two free positions (zero-based) have the listed determinant.

| $\xi$ | First kernel vector | Second kernel vector | Free positions | Minor |
|---|---|---|---|---:|
| $0$ | $(-10,35,-28,35,-112,84,0,0,0)$ | $(-10,35,-28,0,0,0,98,-294,210)$ | 5, 8 | $-75600$ |
| $1$ | $(-4,7,0,35,-56,0,-56,84,0)$ | $(-9,7,14,70,-28,-126,-98,0,210)$ | 7, 8 | $-15120$ |
| $1/2$ | $(1,-7,7,0,35,-42,-35,42,0)$ | $(24,-133,126,-105,826,-840,-294,0,420)$ | 7, 8 | $-483840$ |

The absolute values of these minors are
$2^4 3^3 5^2 7$, $2^4 3^3 5 7$, and $2^9 3^3 5 7$, respectively.
For a combination with coefficients $s,t$, rank one would force:

* At $0$: $st=0$, $s(s+t)=0$, and $t(s+t)=0$, so both are zero.
* At $1$: $t(s+11t)=t(s+5t)=0$. Their difference gives $6t^2=0$,
  hence $t=0$; another minor gives $3s^2=0$.
* At $1/2$: $(s+10t)(2s+33t)=0$ and
  $s^2+26st+156t^2=0$. If $s=-10t$ the second gives $-4t^2=0$.
  On the other branch, subtract $(2s+19t)(2s+33t)$ from four times
  the second expression to get $-3t^2=0$.

This also excludes nonzero rank-one products at each exceptional clock,
in every compatible characteristic. Thus the physical overlap needs
at least one row between the two pivots.

## Exactly four zero diagonals versus additional zeros

When there are exactly four, their chronology is the original first
zero row, the two separated interior pivots, and the original last zero
column. In fact the Volterra commutator has **nullity exactly four and
semisimple zero** in this branch. Eliminate its nonzero-diagonal
principal block, leaving a strictly lower triangular Schur complement
on the four zero sites $0,i,j,t$. Since $R\mathbf1=0$, the effective
row at $i$ vanishes. The forward kernel vector has $v_0=0$ and
$v_i\ne0$, so the effective $(j,i)$ entry vanishes, and $R\mathbf1=0$
kills the rest of row $j$. The exact backward relations give $\beta R=0$;
$b_t\ne0$ then kills the final effective row. The Schur complement is
zero, proving the nullity assertion. This concerns $R=CA-AC-A^2$, not
the generalized zero eigenspace of $A$ itself.

On an ordered field, let $r$ be the reduced tall denominator degree,
and $\ell$ the last nonzero zero-eigenvalue contribution to the tall
polynomial part, zero if that part has no positive degree. The degree
of the reduced numerator is at most $r+\ell$. The existing split-pole
tall bound requires $r+\ell\ge9$ at order ten. Thus exactly four zeros
force $\ell\ge2$ (as $r\le7$), while five or more zeros force
$\ell\ge3$ (as $r\le6$). No independent upper bound of four zeros
or contradiction for the branch with additional zeros is proved here.

The exact rational [tall-only control](check-dirk10-tall-four-zero-control.py)
has eleven physical rows with zero diagonals at stages 1, 5, 7 and 11.
It satisfies C(2), D(1), D(2), the same endpoint conditions, the
semisimplicity of $R$ at zero, and every tall condition through order
ten. All rooted trees through order six pass independently, but the order-seven tree read $\beta C^3 A c^2=1/21$ fails.
The construction freezes the two blocks across a chronological cut.
The remaining cross-block edits preserve the linear simplifying
conditions; two such edits in one word vanish by triangularity.
The five remaining tall equations and the one interior Schur equation
are therefore exact linear equations for the edit. Its reduced tall numerator and denominator have degrees 11 and 7: all four zero-eigenvalue dimensions of A are used by an observable length-four chain, despite the semisimple zero of R. This control is
not assumed to have the genuine order-ten cubic flag ranks or mixed
reads, and is **not** a candidate order-ten tableau.

## Lean verification

[DIRKAdjacentCubicScalar.lean](../../lean/RKCert/ReviewedNative/DIRKAdjacentCubicScalar.lean)
checks the integer elimination explicitly, with separate exceptional
proofs and paid divisor factorizations.
[DIRKOrderTenCrossedZeros.lean](../../lean/RKCert/ReviewedNative/DIRKOrderTenCrossedZeros.lean)
connects the actual native profiles to that system and proves
crossed_zero_sites_buffer and crossed_nonunit_sites_buffer.
The new scalar/native files and the
[axiom audit](../../lean/AuditReviewedNativeDIRKOrderTenCrossedZeros.lean)
were run with Lean/Mathlib 4.36.0. The Schur split and tall numerator
observations immediately above are mathematical deductions, not
additional native Lean endpoints.
