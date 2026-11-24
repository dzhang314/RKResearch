# Unrestricted DIRK: native inclusive Hermite gains and both grade-six head profiles

All eight small modules were built on pinned Lean/Mathlib 4.36.0 against the reviewed
`RKResearch.FiniteRootedTree`, `Φ`, and `HasOrder` from human commit
`91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5`. The source and audit live
under `ai-generated/lean`; the human core and old p15 certificate are unchanged.

* `ClockBlockDetection` proves a paid nodal obstruction for any physical clock
  invariant subspace of the actual grade. Even in admissible positive characteristic,
  a single grade-j probe and exact order 2r force at least r unmatched nonzero
  clock blocks. The proof tests a common lifted nodal polynomial directly with the
  reviewed shifted Cauchy system; it never assumes distinct clocks or nonzero weights.
* `DIRKPrefixHermite` gives the incoming and outgoing Hermite dimension gains,
  retaining the diagonal entry at the last detecting row. The only old-name import of the inclusive test
  is the unchanged wholly tree-independent `RKCert.NodalHermiteRank` and its
  Mathlib-only dependency `RKCert.NodalPrimitive`. The primitive used in the
  rank argument and its defect membership are the native reviewed ones.
* `DIRKGradeSixBand` proves that for order p>=7 over every characteristic-zero
  field, failure of dim F6 >= dim F3 + 4 forces all three rank increases to equal
  one and forces F4, F5 and F6 each to escape under multiplication by the clock.
  In particular the full extra dimension is proved whenever any one is invariant.
  The two surviving head profiles must still be eliminated for an unconditional
  surplus. This result does not claim the 20- or 21-stage order-15 endpoint.

* `ClockHeadFibers` localizes the original clock head by *unpaid* clock blocks
  modulo the invariant core. Already-paid blocks never contribute; no preliminary
  normalization or sign assumptions are needed. It imports the shared
  `NativeClockStaircase` and reuses the Mathlib-only `RKCert.OneEscape`.
* `ClockHeadSupport` supplies one representative of the same chain away from
  all live core coordinates and the polynomial degree cost of its multiplier.
* `DIRKGradeSixHeads` checks both surviving structural alternatives. If F3 is
  clock-invariant, it is closed under pointwise multiplication and one grade-4
  head extends through F6 on at least four escaping numerical clock blocks.
  Otherwise an invariant multiplicatively closed core and one physically disjoint
  head generate all of F3 through F6. For some r>0, the head has >r+3 distinct
  physical clocks and agrees wherever nonzero with a nonzero polynomial P satisfying
  deg(P)+r<=4. These are derived from the reviewed tableau; the four-debut and
  five-donor head exclusions are not part of this packet.

* `C2CubicFlag` proves F3 is *exactly* the span of the actual cubic defect when
  C(2) holds. This span identity is valid over every commutative ring and does
  not assume order, triangularity, or characteristic zero. It relies on the
  existing verified constructor-order tree enumerator, not another tree type.
  At order >=3 an unrestricted DIRK over a field then has exactly rank one
  at F3, with a nonzero cubic defect.
* `DIRKC2GradeSixHead` specializes the hard early branch: when C(2) holds,
  F3 is clock-noninvariant, and the surplus fails, the actual cubic defect
  (not just some chosen representative) generates F3,F4,F5,F6 as clock
  chains of lengths 1,2,3,4 over the zero core. Its nonzero values at
  more than four distinct physical clocks coincide with a nonzero polynomial
  of degree at most three. The later four-start case is not identified with C(2).

The independently staged `RKCert.ReviewedNative.NativeClockStaircase`
(source SHA-256 ce4951b5ef7b32357bce44dd10062b0330c6078d1e97585be32cff49ee738e03)
is a prerequisite of the three head modules. The three band modules do not
depend on it. In a combined integration, build `ClockBlockDetection` before
the separate strict-tableau `ForwardNodalGain`, which also uses its mask lemma.
Build the eight modules in the order above and run the three audits and the eight
individual kernel replays on the pinned project.

`AuditReviewedDIRKGradeSixBand.lean` checks the order-15 F6-invariant consequence
and lists seven axiom closures. `AuditReviewedDIRKGradeSixHeads.lean`
lists seven more and tests the order-15 four-clock consequence. `AuditReviewedDIRKC2Cubic.lean` checks three more and includes an ordinary-ring
regression over ℤ × ℤ. These 17 listed declarations contain only propext, Classical.choice,
and Quot.sound. Each new leaf also passed an independent `leanchecker --verbose`
kernel replay; evidence is in `evidence/reviewed-dirk15-grade-six`.
