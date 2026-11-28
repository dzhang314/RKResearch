# A native exact-order-12 real DIRK witness with 15 stages

This packet completes the Lean proof for the literal real midpoint tableau
already given as an [exact mathematical construction](../dirk12-fifteen-midpoint-real-upper/README.md).
It is not a new numerical stage bound. The witness has 15 actual rows.
It has a lower triangular \(\mathit{A}\), explicit origin and literal
terminal, and \(A_{1,1}=1/16\) in zero-based indexing. Hence it is ordinary
DIRK, neither explicit nor common-diagonal SDIRK.

The endpoint **Actual.exists_exact_real_dirk12** is unconditional over
\(\mathbb R\). It asserts the existence of the matrix and output
\(\mathbf b\) satisfying the reviewed **HasOrder 12** predicate and
failing **HasOrder 13**. It uses the isolated real root existence theorem,
not a free root or a finite-field inference. The order-13 failure is the
actual directed positive scaled bush defect. The established
[degree-216 characteristic-zero field construction](../dirk12-fifteen-midpoint-degree216-field/README.md)
identifies the algebraic provenance separately; this Lean endpoint is
typed over \(\mathbb R\), not over a formal degree-216 field extension.

## The remaining reverse checks

At reverse grade five the integer-scaled error is
\[
  \widehat{\mathbf E}_5
     =5\mathit{A}^{\mathsf T}\mathbf W(Y^4)-\mathbf W(Y^5).
\]
For input powers \(0\)–\(5\), its scalar pairings reduce by adjointness and
paid integration by parts to the fourth probe of the corresponding actual
forward defects. The lower defective vectors vanish on ordinary stages;
the true quintic profile is proportional to \(X L'_6(X)\), which is
silent to the fourth reflected probe. Both tests use only the paid
scalar degrees.

The seventh test is the actual monic degree-six reflected nodal input.
The [forward fit packet](../dirk12-fifteen-midpoint-native-forward-fit/README.md)
proves its fourth actual reflected primitive read. The largest scalar
degree used is eleven. The lower tests and this monic test imply silence
through degree six without computing five expanded quartic identities.

For \(\mathit{A}^{\mathsf T}\mathbf H\), the same seven scalar inputs
have images silent to \(\mathbf H\): the lower forward defects have
ghost support, the quintic is a degree-six profile off the terminal
and ghosts, and the degree-six nodal input has a true nonterminal
degree-at-most-seven image. Each actual ghost column of this transpose
read is likewise a degree-at-most-seven polynomial tap on the support
of \(\mathbf H\). The terminal column is identically zero.

Finally, the actual ordinary nonterminal annihilator of admission
degree six is exactly the span of \(\mathbf G,\mathbf H,Y\mathbf H\).
Remove the second physical repeat using \(\mathbf G\), fit
\(\mathbf H,Y\mathbf H\) at two distinct representatives with proved
nonzero amplitudes, and use the seven remaining degree-six Lagrange
cardinals. No rank calculation over floating point or residue field is
used. This puts both \(\widehat{\mathbf E}_5\) and
\(\mathit{A}^{\mathsf T}\mathbf H\) in the true reverse fifth band. The
complete low bands and the two actual grade-six bridges now instantiate
the reviewed complementary-support sufficient flag for **every**
rooted-tree condition through order twelve.

## Native audit and prerequisites

The order is **DIRK12MidpointReverseThreeSpan**,
**DIRK12MidpointReverseActualTop**, **DIRK12MidpointRealExactOrder**,
**DIRK12MidpointRealExactOrderAudit**. These depend on the earlier
native grouped reverse, low-adjoint, and forward fit packets.
The final typed audit passes with matched Lean/Mathlib 4.36.0 and only
standard logical axioms. No matched cross-release Mathlib sweep is
asserted here.
