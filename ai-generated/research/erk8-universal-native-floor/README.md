# Universal native ERK8 stage minimum

**Eleven stages are necessary and sufficient at explicit order
eight, over every nontrivial commutative ring in which \(8!\) is a
unit.** At any width \(s\), the literal exact-order-eight predicate
is equivalent to \(s\ge11\) and \(8!\) being a unit. A ring without
this unit has no order-eight method at any width. The lower theorem
excludes even order *at least* eight at widths below eleven.

These are now end-to-end Lean theorems in
**RKResearch.Certified.ERK8Universal**:

- **no_order8_fin10**: no literal strictly explicit width-ten tableau
  satisfying the reviewed HasOrder 8, over any field.
- **stages_at_least_eleven_field**: the width inequality over any field.
- **stages_at_least_eleven**: the width inequality over every nontrivial
  commutative ring, not necessarily a domain, reduced, or ordered.
- **exact_order_eight_exists_iff**: the full width/unit characterization,
  with the verified ninth-order failure included.

## The last branch: outside characteristic 11

The paid width-ten census outside 11 leaves one off or four off.
The [paid one-off packet](../erk8-paid-one-off-native-floor/README.md)
already excludes one off in every field. Its characteristic-eleven
counterpart also closes the full field and ring cases at and above
that nilpotent characteristic locus. This packet closes four off
with \(11\ne0\).

The literal physical placement earns the three clean interior
clocks, the chronological first clean row (4 or 5), and the
terminal profile. Put \(q(u)=7u^2-7u+1\). The three exhaustive
clean-clock orientations \((h,x,z)\) are
\[
 (u,\tfrac12,1-u),\qquad (u,1-u,\tfrac12),\qquad
 (\tfrac12,u,1-u), \qquad q(u)=0 .
\]
Each orientation and its conjugate are handled by exact affine
reductions in \(u\). The fitted defect \(P\) is normalized by a
nonzero scalar; the characteristic-11 scale loss is kept out of
this step and handled by the separate checked branch.

For a positive power of a clean clock, the origin contributes
zero to the top-coefficient measure. After canceling the clock
factor in each other cofactor, the clean factors are
\(3/14,-3/28,3/14\) at \(u,\tfrac12,1-u\).
Writing \(A_u,A_v,A_m\) for the three normalized defect evaluations,
the common cleared numerator for exponent \(r\) is
\[
 (2u)^r A_v A_m + (2(1-u))^r A_u A_m - 2 A_u A_v .
\]
The direct identities transport these cleared numerators to the
actual chronological Newton rows, and produce the three scalar
tests for the early clean placement and the two late clean placement
factors. The notation \(A_u,A_v,A_m\) here denotes scalars; the
original RK tableau is still the matrix \(A\).

Outside the paid factorial primes, the possible scalar norm losses
are exactly \(11,17,37,41,43,79\). The generic proof pays every
nonzero factor outside this list. At each of \(17,37,41,43,79\),
both possible roots of \(q\) and all three chronological orientations
are checked by explicit integer congruences in Lean; this is valid
in arbitrary extensions because these two roots exhaust the
quadratic. The exceptional repairs are:

- At \(17,43,79\), a normalized quadratic shares at most one
  clean root. If the actual terminal equality \(Q+P R_2=\sigma D\)
  has nonzero \(\sigma\), the shared root also lies on the off hull
  \(D\), contradicting the nonzero fitted off value. If
  \(\sigma=0\), then \(P\) divides \(Q\), and coprimality with the
  other three clean factors would make it divide a linear factor.
  This is impossible for a quadratic.
- At \(37,41\), the exceptional head is genuinely linear.
  The terminal multiplier is one by the degree-four monic
  coefficient; the clean/off transfer uses constant quotients.
  The degree-four coefficient of the tested monomial cancels
  between the two monic hulls. The first clean row 4 still has
  its usual nonzero test. At first clean row 5 the clean moments
  are a nonzero geometric sequence, so the two actual Newton
  equations would identify the distinct scalars \(1/2,1/3\).

No exceptional prime remains. The proof uses exact algebraic
identities, not a bounded tableau search or a claim that all
coefficients lie in a prime field.

## From fields to rings and exact order

Appending zero-weight isolated stages makes the width-ten field
exclusion apply at every smaller width. A maximal residue field of
a nontrivial commutative ring preserves the literal rooted-tree
equalities, strictness, and stage count under the unital coefficient
map, so the universal field lower bound descends to the original
ring. The tallest order-eight tree makes \(8!\) a unit in the
original ring. The separate verified eleven-stage tableau exists
over every such ring, with exactness proved by two ninth-order
residuals and a Bézout identity; padding keeps that exactness.

## Reproduction

From ai-generated/lean with the matching Mathlib checkout:

    lake build +RKCert.ReviewedNative.ERK8UniversalStageFloor

The adjacent Lean 4.36.0 replay prints the exact endpoint axiom
sets. They contain only propext, Classical.choice and Quot.sound.
The source hashes and an independent standard-library exact
arithmetic replay are adjacent:

    python3 replay_affine_guards.py

This packet does not claim a whole dependency build on other
Lean versions.
