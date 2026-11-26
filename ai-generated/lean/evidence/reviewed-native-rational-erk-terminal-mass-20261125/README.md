# Checked rational terminal-mass construction

The [native module](../../RKCert/ReviewedNative/RationalERKTerminalMass.lean)
builds a terminal block over \(\mathbb Q\) from actual paid donor rows.
Let \(q_A\coloneqq 2A(A\mathbf 1)-(A\mathbf 1)^2\), with the square taken
componentwise. The contrast row \(\eta\) has nonzero gain
\(g\coloneqq\eta q_A\), and each baseline row \(D_x\) has zero gain on
that same defect. For distinct interpolation samples \(\lambda_\ell\)
the new row at label \((x,\ell)\) has old-coordinate entries
\(D_{xi}+\lambda_\ell\eta_i\). The matrix has the literal block form

\[
M\coloneqq\begin{pmatrix} A & 0 \\ B & 0\end{pmatrix},
\qquad
B_{(x,\ell),i}\coloneqq D_{xi}+\lambda_\ell\eta_i.
\]

The old stages get zero weights. At each output label \(x\), the
weights across its samples have zeroth moment \(\beta_x\), first
moment \(\omega_x/g\), and all higher supplied moments zero.

The main theorem, realize_quadratic_outgoing_mass, assumes \(p\ge4\),
the actual RowLaw on the donor trees of order less than \(p\), and
quietness of \(\eta\) on actual trees of order at most two. It also
assumes the baseline and contrast gain conditions above, the paid
annihilation \(\sum_x\omega_x c_x^k=0\) when \(k+4\le p\), and the
prescribed quadrature \((k+1)\sum_x\beta_xc_x^k=1\) when \(k+1\le p\).
Under those hypotheses, the constructed pair \((M,b)\) satisfies the
literal reviewed predicate RKResearch.HasOrder p M b and, with

\[
c_M\coloneqq M\mathbf 1,\qquad
q_M\coloneqq 2M c_M-c_M^2,
\]

it satisfies
\[
\sum_{i:\,(c_M)_i=z} b_i(Mq_M)_i
  =\sum_{x:\,c_x=z}\omega_x
\]
for every rational clock \(z\). Both sides sum over all matching
labels, including repeated clocks. This is a statement about the
actual outgoing matrix-vector product, not a proxy column.

The [unchanged typed audit](../../AuditReviewedNativeRationalERKTerminalMass.lean)
packs that same block and weights into an existential, checks the
native order predicate, and expands the actual clock, defect, and
weighted outgoing sum. The [portable audit transcript](typed-audit-output.txt)
keeps the exact named report for realize_quadratic_outgoing_mass and
its stock axioms: propext, Classical.choice, and Quot.sound. The
only replacement in that transcript is the scratch path of one
nonfatal unused-simp-argument warning.

## Measurement and scope

The repaired body and the separate no-output typed audit both exited
zero with Lean 4.36.0 and Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842.
The body loaded nine previously measured project modules. The audit
loaded the same 45 companions plus the five exact fragments of the
repaired body, and produced no object. The
[portable acceptance record](acceptance.json) identifies the exact
sources, provider and report digests, and the earlier failed body as
a separate attempt that supplied no objects. No binary is included.
This was not a cold package build.

The conclusion is conditional on the stated actual donor and moment
hypotheses. It is not an unconditional donor-chain construction, a
strictness or positivity certificate, a stage bound, a claim of
failure at order \(p+1\), or a claim about a particular tableau.

Source digests may be checked from the repository root:

    sha256sum -c ai-generated/lean/evidence/reviewed-native-rational-erk-terminal-mass-20261125/checked-sources.sha256
