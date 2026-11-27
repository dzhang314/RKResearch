# Literal Lean certificate for universal fifteen-stage ERK9

The closed endpoint is
**RKResearch.Certified.ERK9UniversalFifteen.exists_exact**. In every
nontrivial commutative ring, a unit \(9!\) supplies a strictly lower
\(15\times15\) matrix \(A\) and weight vector \(\boldsymbol b\) with
HasOrder 9 and without HasOrder 10. No field, characteristic, or
locality hypothesis occurs. The companion
**exists_exact_iff_factorial_unit** also proves necessity from the
tall order-nine condition. It is an equivalence at width 15, not a
claim that width 15 is minimal.

The certificate uses the integer-scaled literal matrix in tableau.json
and the independently reviewed rooted convention. The closed receipts
check 274 normalized derivative profiles, 132 matrix action vectors,
all 586 profile joins, and the resulting order conditions. The whole
tree family is covered by the existing normalized-vector induction.
The primitive-splice explanation is not an axiom of the native proof.
The tenth bush has a kernel-checked cleared discrepancy:
after multiplying by 23328 the residual is \(-7\). Since seven divides
the invertible common denominator, this cannot vanish in the stated
coefficient rings. The final endpoint also checks that the denominator
2116800 divides \((9!)^2\).

Replay from ai-generated/lean with the repository's matching Mathlib:

    lake build +RKCert.ReviewedNative.ERK9UniversalFifteen

The arithmetic cache is untrusted. To regenerate its deterministic data
and block-check modules, run generate_lean.py with --source pointing to
tableau.json, --emit pointing to lean/RKCert/ReviewedNative, and
--modules pointing to a scratch file. The handwritten proof core and
top-level endpoint are not overwritten.

The included audit used Lean 4.36.0 and pinned Mathlib. It reports
only propext, Classical.choice and Quot.sound. There is no claim here
of a completed build on other Lean versions.
