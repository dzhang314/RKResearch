# Native forward completion of the real 15-stage midpoint DIRK12 tableau

All statements in this packet concern the actual weighted physical matrix
\(\mathit{A}\) from the [grouped reverse assembly](../dirk12-fifteen-midpoint-native-reverse/README.md).
The [native low reverse primitives](../dirk12-fifteen-midpoint-native-low-adjoint/README.md)
are used as proved identities, not hypotheses on a new tail.

## Low and entering-quintic forward profiles

The verified five opening rows and the actual low adjoints suffice to finish
the remaining four nonterminal ordinary rows. For entering powers \(1\)–\(4\)
the forward primitive defect vanishes at every nonterminal ordinary row,
including the origin. The repeated pair agrees by the actual
\(\mathit{A}^{\mathsf T}\mathbf G=(d/2)\mathbf G+\mathbf H\) relation.
Three actual reflected pairings at exponents \(1,2,3\) separate the three
remaining nonzero distinct ordinary labels, with the two equal signed
weights added only in the pair average. The genuine terminal proof
then completes the required forward-band membership through entering
power \(4\).

For entering power \(5\), with the existing integer-scaled forward
primitive definition, the exact nonterminal ordinary profile is
\[
   \operatorname{forward}_5(i)
     =6(1/2)^6(\epsilon+\Delta)\nu\,c_i L_6'(c_i),
   \qquad \Delta=5/11088 .
\]
It is paid on all five opening rows, including the first live row where
\(L_6'(1/2)=0\), and the same three-clock argument completes it on the late
ordinary rows. Its actual weighted output is zero. Consequently the true
quintic grade-six bridge is proved as soon as the reverse grade-five
space is known to vanish at the ghosts and terminal and annihilate
ordinary degree at most six. The profile and its output themselves
have no such additional premise.

## Literal degree-six nodal input and fourth probe

Let \(Q^\#(Y)\) be the monic reflected degree-six hull through the
ordinary origin and the five actual opening labels. Write
\(\mathbf q=Q^\#(\mathbf 1-\mathbf c)\). The formula for the true
nonterminal ordinary action is
\[
  (\mathit{A}\mathbf q)_i
   =\left[\Lambda(u-Y)Q^\#(Y)+G_{\rm tap}(Y)\right]_{Y=1-c_i}.
\]
Here \(G_{\rm tap}\) is the degree-at-most-seven polynomial obtained
by applying the two literal ghost-tap modes to the four actual inputs
\(q_g\); the scalar coefficients use \(\sum_g\ell_gq_g\) and
\(\sum_g\ell_g c_gq_g\), not a fitted arbitrary polynomial.
The nodal polynomial kills every actual ordinary donor of the first
five rows and the origin. Entries after those donors are zero by
literal triangulation. The true pair equality and first three adjoint
probes therefore identify this image on the four late ordinary rows.

Put \(J_1Q^\#(Y)=\int_Y^1Q^\#(s)\,ds\). The true fourth read is
\[
 \mathbf W(Y^4)^{\mathsf T}\mathit{A}\mathbf q
      =\mathbf W(Y^4)^{\mathsf T} (J_1Q^\#)(\mathbf 1-\mathbf c).
\]
This is actual tableau equality, not just a probe of a proposed
profile. Terminal and ghost weights disappear in each positive
reflected read for their respective proved reasons. The fourth
pairing of the nodal correction uses degree \(4+7=11\), exactly the
fourth moment relation already paid by the degree-36 root model.
The actual ghost polynomial is silent in the same paid degree range.

## Native audit

Dependency order: **DIRK12MidpointForwardActualLow**,
**DIRK12MidpointPolynomialVector**, **DIRK12MidpointNodalFourthProbe**,
**DIRK12MidpointForwardActualNodal**, **DIRK12MidpointForwardFitAudit**.
The typed audit uses matched Lean/Mathlib 4.36.0 and standard logical
axioms only. No matched cross-release sweep is asserted. This packet
does not by itself assert the final reverse grade-five span or the
complete native order-twelve theorem.
