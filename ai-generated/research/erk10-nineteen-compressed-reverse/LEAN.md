# Literal Lean certificate for nineteen-stage ERK10

**RKResearch.Certified.ERK10UniversalNineteen.exists_exact**
gives a strictly lower \(19\times19\) matrix \(A\) and weight vector
\(\boldsymbol b\) of order ten and not order eleven over every
nontrivial commutative ring in which \(10!\) is a unit.
**exists_exact_iff_factorial_unit** also gives the converse
necessity at width 19, through the tall tree. This is not a
statement of minimal width.

The kernel checks the integer-scaled literal tableau using 582
normalized stage profiles, 274 action profiles, and 1,328
ordinary-rooted joins. The heuristic or symbolic weighted reverse
construction is not a proof dependency. For exactness it checks
\(64\) times the eleven-vertex residual equals \(35\);
\(35\) is a unit since it divides the invertible common denominator.
The closure checks this denominator divides \((10!)^6\).

Replay from ai-generated/lean using the repository's matching
Mathlib:

    lake build +RKCert.ReviewedNative.ERK10UniversalNineteen

The deterministic generate_lean.py creates the class tables and
bounded join receipts. The certificate includes smaller join
slices to limit peak memory; these glue in Lean and ultimately
cover the full reviewed tree recurrence.

The end-to-end check ran on Lean 4.36.0, with only
propext, Classical.choice and Quot.sound. The arithmetic and
Lean source manifests are separate. Other Lean versions are
not claimed to have been replayed here.
