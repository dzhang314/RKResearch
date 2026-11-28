# The paired pool can have zero total

The [regular](README.md) and [zero physical opening score](ZERO-OPENINGS.md)
proofs exclude the same triple-and-pair chart with **all physical
scores and any total at the pair \(b\)**, provided the triple
total \(W_a\) is nonzero. All endpoint, physical chronology and
paid-field guards remain unchanged. The surviving pooled-mass
question is \(W_a=0\); this note does not assert that a zero-total
triple can be treated as a single donor.

If \(W_b=0\), its two scores are opposite, as are the two corresponding
coordinates of every \(D_3\) profile. At a row \(i\) replace its
contributions on any scalar or \(D_3\) input by its first-copy
coordinate times \(K_{i,b_1}-K_{i,b_2}\), using zero for a causally
absent column. This folding is valid even if the two scores are zero
and the mode coordinates are nonzero. Thus an early \(b\)-closure
does not introduce any new effective donor in these tests.
Its zero aggregate itself need not be a target.

These are the places to check in the earlier proof:

* The first two ordinary targets still exist by scalar support.
  In the no-leakage case, before the first such target only
  \(a_1,a_2\) and the single folded \(b\)-coordinate can be
  nonzero-ordinate donors. If the first target is a singleton,
  its row and the old part of the next target's row annihilate
  the same effective three-coordinate \(D_3\) restriction:
  folded \(b\) is genuinely one coordinate irrespective of when
  the closure occurs. Thus the rank-two and proportionality
  arguments are unchanged. If the first target is a repeated
  label, only the triple can be such a target with \(W_b=0\);
  the same cubic double-root argument applies.
* In leakage supported on only one label, use the first live
  clean target outside that label as in the zero-opening note.
  The strict single-label Krylov block and subsequent feedback
  use total taps at a scalar label, and allow two copies of a
  clean label; no division by its group total is needed.
* When separate modes exist, a live physical \(b_1\) is
  normalized as before. Thereafter its entire folded mode
  tracks the weighted scalar \(b\)-tap, since both scores
  are opposed. With \(w_{b_1}=0\), both scores are zero and
  there is no scalar \(b\)-tap to track. The ordinary and virtual
  comparisons at \(a_2\) therefore remain calibrated away
  from the first ordinary target's label. In particular a
  zero-total \(b\)-closure between these tests does not introduce
  a second uncalibrated scalar donor.
* In the exceptional prefix computations, \(\alpha\) and the
  current \(b\)-tap are evaluated after folding. When
  \(b_1\) precedes the first \(a\)-copy, either one or both \(b\)
  copies may already be present, but both their weights and
  their \(\boldsymbol u,\boldsymbol g,\boldsymbol h\)
  values are proportional to the first-copy coordinate.
  Hence the displayed multipliers and exact exceptional
  determinant do not change. When \(a_1\) precedes \(b_1\),
  the \(b_1\) row can still only use the first \(a\)-copy.
  After folding, the two exceptional mean identities hold
  at any subsequent ordinary group with old labels \(a,b\),
  regardless of early completion of \(b\). The forced first
  triple closure \(a\) and contradiction at the second
  target are unchanged.

The fold is an identity for the low-word source columns,
not a claim that physically deleting a \(b\)-copy preserves
all rooted-tree order conditions.
