# Literal Lean certificate for seventeen-stage ERK10

**RKResearch.Certified.ERK10UniversalSeventeen.exists_exact**
gives a strictly lower \(17\times17\) matrix \(A\) and weight
vector \(\boldsymbol b\) of order ten and not order eleven
over every nontrivial commutative ring in which \(10!\) is
a unit. **exists_exact_iff_factorial_unit** also proves
factorial necessity at width 17 by the tall tree.
This is not a minimal-width theorem.

The kernel checks 759 normalized stage profiles, 327 actions,
and 1,468 ordinary-rooted joins on the integer-scaled literal
coefficients. The selected eleven-vertex tree has a separate
native receipt: \(77760\) times its normalized residual is
\(-1\). The common scale \(800150400\) divides \((10!)^3\).
The native proof does not assume the weighted reverse derivation,
the affine rank solve, or the row merge argument.

Replay from ai-generated/lean with the repository's matching
Mathlib:

    lake build +RKCert.ReviewedNative.ERK10UniversalSeventeen

The deterministic generate_lean.py takes the fixture via --source,
the output ReviewedNative directory via --emit, and a scratch
module-order file via --modules. Its generated values are not
trusted: the bounded arithmetic receipts and the structural
tree cover are both kernel-checked. The included end-to-end
audit used Lean 4.36.0 and reports only propext,
Classical.choice and Quot.sound. Other releases are not
claimed to have been built here.
