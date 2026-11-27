# ERK order eight: characteristic-zero stage floor without an order on coefficients

**Later result.** The [paid extension](../erk-eight-finite/README.md) covers all admissible fields except characteristic 11, and rings with nonnilpotent 11.

**Result (source-level floor):** eleven is the minimum ERK stage count over
every characteristic-zero field. More generally, for a nontrivial
characteristic-zero commutative ring \(R\), a method exists precisely when
\(8!\) is a unit, and in that case the minimum is eleven. The construction
is the separate kernel-checked eleven-stage factorial-localized tableau;
this packet removes order on coefficients from the mathematical lower proof.

**Native scope:** the new four-site and no-double scalar gates are
kernel-checked. The physical rank, repeat, rows, placement and adapter were
re-elaborated without ordered coefficients. The assembled
actual_normalized_head_of_order8_four_off theorem goes from literal strict
Fin 10 order and four-off census to the physical placement, normalized
quadratic head and actual terminal profile. The existing terminal scalar
gates are already characteristic-zero field theorems. The Newton
transfer from tableau to scalar gates, and the full one-off physical
contradiction, remain source proofs. This packet does not claim an
end-to-end native eleven-stage lower bound.

Here \(A\) is the strictly lower coefficient matrix, \(\boldsymbol b\)
its output vector, \(\boldsymbol c=A\boldsymbol 1\),
\(\boldsymbol g=A\boldsymbol c-\boldsymbol c^2/2\), and \(E_j,F_j\)
the graded actual tree and zero spaces. Powers on vectors are
componentwise. “Clean” and “off” mean, respectively, \(g_i=0\) and
\(g_i\ne0\); tags distinguish these cases at coincident clocks.

## 1. Census and one-off branch

The reviewed native order8_native_one_or_four_with_horizon takes
strict Fin 10 HasOrder 8 under exactly Field and CharZero. It supplies the
even horizon and the one-or-four off census; the four-off branch has five
clean tags. In particular the factor and rank calculations putting the
problem in this split do not compare coefficients.

The mathematical proof in
[one-off.md](../erk-eight-stage-floor/one-off.md) is already over an
arbitrary characteristic-zero field, as it states. Its paid profile,
reverse budget, physical selector and one-off prefix arguments form
identities, rank inequalities of finite-dimensional spaces, and
comparisons of **physical indices**. The one-off native helpers
OneOffConstantAmplitude, OneOffGlobalNormal, OneOffCleanClocks,
OneOffPrefixSelectors and OneOffNormalScalars likewise use no field
order. The source proof's final root contradiction concerns \(d,2d\);
it may be replaced verbatim by the no-double calculation below. Neither
a real embedding nor a positive choice of root is used in this branch.

## 2. Five clean tags: replace the positivity step

In the four-off branch, the native measured rank and tagged
interpolation give \(E_5\) equal to the nine-tag value space, and the
terminal coordinate \(\boldsymbol e_9\in E_4\) is the unique physical
clean tag at clock \(1\), with nonzero weight. The four off aggregates
vanish. Thus the five clean aggregates reproduce all scalar moments
\(m_k\) for \(0\le k\le7\).

It remains important that every clean aggregate is nonzero. The
previous proof used the positivity of the integral of
\((1-X)D(X)^2\). The following instead uses exact moments, with no
order on the coefficients and no positivity of weights.

If a nonterminal clean aggregate vanishes, let \(a,d,e\) be the
remaining three possible clean sites apart from the terminal \(1\).
Put \(D=(X-a)(X-d)(X-e)=d_0+d_1X+d_2X^2+X^3\).
The four polynomials \(X^k(1-X)D\), \(k=0,1,2,3\), vanish
wherever the contributing rule has a nonzero weight, and have degree
at most seven. Write \(\beta_j=m_j-m_{j+1}\). The rooted bush tests give
\((j+1)(j+2)\beta_j=1\) for \(0\le j\le6\). Multiplying the
four identities \(\sum_{l=0}^{3}d_l\beta_{k+l}=0\) by \(60,60,420,840\)
respectively (where \(d_3=1\)) gives the four integer rows
\[
 \begin{pmatrix}
 30&10&5&3\\
 10&5&3&2\\
 35&21&14&10\\
 42&28&20&15
 \end{pmatrix}
 \begin{pmatrix}d_0\\d_1\\d_2\\1\end{pmatrix}=0.
\]
The row combination \((-14,210,-90,35)\) extracts \(3\), a
contradiction since the third bush quadrature identity makes \(3\) a
unit. No separability or distinctness of \(a,d,e\) is needed by this
standalone lemma. It works even over a nontrivial commutative ring;
the surrounding physical rank arguments use field structure.

This is no_four_sites_at_one in ERK8UnorderedScalarGates. The
re-elaborated rank data derives its input quadrature directly by
subtype summation over the original **clean tags**, using actual off
mass cancellation. The remaining physical lemmas use comparisons
only in Fin 10, not in the field. The checked placement gives the
unique repeat at row \(8\), clean rows \(6,7,9\), and first nonzero
clean row \(4\) or \(5\). In particular the argument neither merges
rows nor ignores an off tag at the same clock as a clean tag.

## 3. Actual clean polynomial and its algebraic charts

Write the three chronological clean interior clocks as \(h,x,z\). The
degree-seven polynomial probes identify their cubic
\[
  L(X)=(X-\tfrac12)(X^2-X+\tfrac17),\qquad Q(X)=X L(X).
\]
The terminal profile gives an actual polynomial \(R_2\) of degree at
most two such that
\[
 Q(\boldsymbol c)+\boldsymbol g R_2(\boldsymbol c)=Q(1)\boldsymbol e_9 .
\]
The normalized quadratic head \(P\), with \(g_i=P(c_i)\) at all off
rows, follows from the clean primitive tests and chronology, not from
a proposed numerical clean shape:
\[
\begin{split}
 P(X)&=\Theta(X-x)(X-z)+
   \kappa(5X^2-(4x+3h)X+2hx), \qquad \kappa\ne0,\\
 \Theta\left(h/4-(x+z)/3+xz/(2h)\right)&=\kappa(x/3-h/4).
\end{split}
\]
The native CleanPrimitivePlacement, terminal profile, and
NormalizedShape bundle includes the five clean tags, actual shape,
nonzero quadratic leading coefficient and \(P(0)P(h)P(x)P(z)\ne0\).

Here is precisely how the scalar algebra works in an arbitrary
characteristic-zero field. The clocks are three distinct roots of \(L\),
so one is \(1/2\) and the other two are roots \(u,1-u\) of the quadratic.
Take \(\omega=1-2u\) **in the given coefficient field**; its square is
\(3/7\). This sets \(L_0=(1-\omega)/2, C=1/2,R_0=(1+\omega)/2\);
\(L_0,R_0\) name algebraic roots, not smaller and larger roots.
The triples \(L_0 C R_0,L_0 R_0 C,C L_0 R_0\) and the substitution
\(\omega\mapsto-\omega\) cover all six physical chronologies. For
any rational pair \(a,b\) in the exact table, the nonvanishing check is
the nonzero rational norm
\[
 (a+b\omega)(a-b\omega)=a^2-\tfrac37 b^2 .
\]
If the coefficient field has no such roots, the four-off grid is
already impossible. If it does, no extension or selection of a real,
positive, or ordered square root is needed.

## 4. Source-level Newton closure (the remaining native bridge)

The polynomial proof in [four-off-closure.md](../erk-eight-stage-floor/four-off-closure.md)
is field-algebraic in this step. Denote by \(D\) the hull of the four
off clocks in their **physical first-occurrence** order \(a,b,d,e\),
and \(N_j\) the hull of the first \(j\). The actual terminal profile
gives \(Q+P R_2=\sigma D\) for \(\sigma\ne0\), since \(P\) is
nonconstant and nonzero at every root of \(Q\), so cannot divide it.
The top Lagrange coefficients \(L_{j,r}\) of \(X^r/P\) on the first
\(j\) off nodes transfer to the corresponding clean coefficients
\(C_r\) on \(0,h,x,z\) by
\[
       L_{4,r}=\sigma C_r,\qquad
       L_{3,r}=\sigma(C_{r+1}-eC_r).
\]
Indeed, if \(U_D,U_Q\) interpolate \(X^r/P\), then
\(PU_D-X^r=DV_D\), \(PU_Q-X^r=QV_Q\) with \(\deg V_D,\deg V_Q\le1\).
Modulo \(P\), \(D(V_D-\sigma V_Q)=0\). Coprimality follows from
\(P\) nonzero at the known roots of \(D\); nothing requires factoring
\(P\) or extending the field. Comparison of degree five and elimination
of the last off summand give the two identities.

The actual off-only action on \(N_0,N_1,N_2,N_3\) is a Newton
shift of one degree, by causality and the two native bands.
Taking cubic coefficients on the actual pure inputs of powers
one, two and three gives
\[
 \delta(C_r-eC_{r-1})+T h^{r-1}=C_r/r\qquad (r=2,3,4).
\]
Here \(T\) is the single possible tap from clean \(h\) into the last
early off row, and is zero if the first clean row is physical \(5\).
No assumption on the nonvanishing of \(\delta\) occurs.

* For first clean at \(4\), its three early off taps kill \(1,X\)
  on normalized off inputs, so its clean primitive equations replace
  \(C_r-eC_{r-1}\) by an \(r\)-independent nonzero multiple of
  \(h^r/r\). Eliminating the two parameters gives
  \(C_4-2hC_3+h^2C_2=0\). The actual \(P\) makes the left side
  \(-(4z-2h)/P(z)\), so \(h=2z\).
  The order-free no-double gate excludes \(t\) and \(2t\) both
  solving \((2X-1)(7X^2-7X+1)=0\): \(t=1/2\) would make
  the value at 1 nonzero; \(2t=1/2\) and \(7t^2-7t+1=0\)
  would imply \(5=0\); if both roots satisfy the quadratic,
  subtraction gives \(14t=3\), then \(35=0\). The native lemma
  actually needs only nonvanishing 5 and 7 in the field.
* For first clean at \(5\), the consistency determinant is
  \((C_1C_3-C_2^2)(C_4-2(p_0/p_2)C_2)\).
  It cannot vanish, by the exact six-orientation algebra described
  above. The shipped scalar firstCleanAt4_contradiction and
  firstCleanAt5_contradiction already express both endpoints over
  Field and CharZero; they take the corresponding earned
  scalar equations as hypotheses, not literal HasOrder.

This establishes exclusion at width ten after the two tagged cases.
The reviewed StagePadding.strict_stages_gt_of_exact_exclusion then
excludes every smaller width; it does not use coefficient order.

## 5. Descent to rings and remaining scope

Let \(R\) be nontrivial of characteristic zero. Invert the multiplicative
set of all nonzero integer scalars, which does not contain zero.
The resulting commutative ring is nontrivial: if \(1=0\) in this
localization, some member of the multiplicative set would already
be zero in \(R\). Quotient by a maximal ideal. The resulting field
has characteristic zero, because every nonzero integer scalar maps
to a unit, never zero. A strictly lower tableau over \(R\) maps to a
strictly lower tableau over that field; reviewed rooted order
identities are polynomial and hence survive coefficient change.
The field exclusion therefore rules out widths at most ten even
when \(R\) has zero divisors or nonunits among its integers.

The independent eleven-stage construction supplies exact order eight
whenever \(8!\) is invertible. The bush identities themselves force
\(8!\) to be invertible for any order-eight method. No corresponding
positive-characteristic lower is claimed by this packet. In particular,
this argument does not infer impossibility in a finite field by lifting
its coefficients to characteristic zero.

## Lean verification

On Lean 4.36.0 with the matching mathlib, re-elaborate the files under
lean/RKCert/ReviewedNative in the dependency order
ERK8UnorderedScalarGates; ERKOrderEightFourOffPhysicalRank, Repeat, Rows,
Placement; ERK8FourOffCleanPlacementAdapter; ERK8UnorderedPhysicalBridge.
The preexisting ERK8FourOffTerminalProfile, ERK8FourOffCleanShapeAlgebra,
ERK8FourOffCleanPrimitive, ERK8FourOffScalar and
ERKOrderEightTaggedCensus are dependencies, not rewritten files. The
two new modules print their theorem axioms. The named native bridge
has no assumed scalar equations beyond literal HasOrder,
strictness and the four-off branch count. The full mathematical
eleven-stage lower theorem is not exported by these modules.
