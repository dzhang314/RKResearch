# Literal Lean certificate for eighteen-stage ERK10

**RKResearch.Certified.ERK10UniversalEighteen.exists_exact**
gives a strictly lower \(18\times18\) matrix \(A\) and weight
vector \(\boldsymbol b\) of order ten and not order eleven
over every nontrivial commutative ring in which \(10!\) is
a unit. **exists_exact_iff_factorial_unit** also proves
factorial necessity at width 18 using the tall tree. This
does not assert minimal physical width.

The kernel checks 759 normalized stage profiles, 327 actions,
and 1,468 ordinary-tree joins on the integer-scaled literal
coefficients in the fixture. A separate native receipt shows
\(77760\) times the selected size-eleven normalized residual
is \(-1\). The common scale \(800150400\) divides \((10!)^3\).
No symbolic construction claim is a proof dependency.

Replay from ai-generated/lean with the repository's matching
Mathlib:

    lake build +RKCert.ReviewedNative.ERK10UniversalEighteen

The deterministic generate_lean.py writes the data and bounded
receipt modules, taking the literal fixture via --source,
the output ReviewedNative directory via --emit, and a scratch
file via --modules. The included audit used Lean 4.36.0 and
reports only propext, Classical.choice and Quot.sound.
