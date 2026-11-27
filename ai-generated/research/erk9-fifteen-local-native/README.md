# Native fifteen-stage exact ERK9 over factorial-unit local rings

The [second rational chart and its literal integer audit](../erk9-fifteen-local-portfolio/README.md)
are now also certified by closed Lean theorems.

- **RKResearch.Certified.ERK9RationalFifteenSecond.exists_exact_of_unit**
  certifies the full second physical matrix over every nontrivial
  commutative ring paying its explicit common denominator. The two
  tenth-order cleared defects use the bush and the shallower mixed
  bush attachment, with an exact integer Bézout identity.
- **RKResearch.Certified.ERK9FifteenLocalRing.exists_exact_local**
  combines the first and second checked tableaux over any commutative
  local ring paying \(9!\). Its denominator sum has the explicit
  integer Bézout value \(10450944000\), which divides \((9!)^3\).
  Locality therefore pays one of the two original denominators.

These theorems require neither a field nor positivity. They do not
assert a single tableau over the universal factorial localization.
The [finite-characteristic companion theorem](../erk9-fifteen-finite-native/README.md)
now also checks the CRT consequence end to end in Lean.

Replay from ai-generated/lean with matching Mathlib:

    lake build +RKCert.ReviewedNative.ERK9FifteenLocalRing

The supplied generator takes the second literal JSON via --source,
the ReviewedNative directory via --emit, and a scratch output
list with --modules. Every arithmetic fixture used by the
theorem is checked in Lean; the generator is not assumed correct.
The audit ran on Lean 4.36.0 with pinned Mathlib, and both
public endpoints report only propext, Classical.choice and Quot.sound.
