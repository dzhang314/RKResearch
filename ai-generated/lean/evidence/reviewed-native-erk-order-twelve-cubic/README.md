# Native order-12 cubic admission and exclusion of head length three

For a strict reviewed order-12 tableau over any characteristic-zero field
with at most 17 original stages, both F₂ and F₃ belong to the physical
invariant core. The exact forward clock chart now has head length two.
Its F₄ rank is either three or four. These statements use the genuine
human trees, elementary weights, and HasOrder at 91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5.

## Main results

- `Graded.buffered_two_leaks` is a uniform theorem over any field:
  when a true degree-(d+2) buffer splits the paid band, shift the latest
  ordinary probe by the physical clock. A paid degree-(d+3) absorber
  cancels the top coefficient; two actual endpoint zeros and the
  additional shifted ordinary probe force away both leaks. It needs the
  stated rank separation, endpoint, and absorber; no marked p16 case is
  asserted.
- `ERK12.grade_eight_no_double_leak` feeds that theorem with the
  extracted physical terminal mesh, the true T8/T9, and the exact
  rank cap. All cubic-grade multiplier products are then paid in the
  actual head.
- `ERK12.grade_three_in_core` uses two chronological joint-prefix
  failures at distinct, nonzero, mesh-eligible physical clocks and
  the previously checked tree-free five-test scalar certificate.
- `ERK12.exclude_paid_cubic_profile` needs only the paid weighted
  columns and an actual stable degree-at-most-three profile. It
  also covers the first two physical members of the head in the
  rank-(3,4) branch. `ERK12.exclude_three_four` rules out that branch
  directly using the intrinsic head; it does not alter support or
  assume a disjoint head representative.
- `ERK12.remaining_rank_two_branches` and the independent cap consumer
  reduce the sharp width-17 exclusion to `(r, dim F₄)=(2,3)` or
  `(2,4)`. Those two branches and the ≥18 endpoint are not asserted here.

## Provenance and verification

Pinned Lean 4.36.0; Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842.
The earlier forward packet SHA-256 is
d5abb8f4888f536710d74e0114f8b5e9af2662c5166f018efee980569d572994.
The only newly consumed non-native modules are the tree-free
`RKCert.OrderTwelveArithmetic` and `RKCert.OrderTwelveGhost`, loaded
from exact cached objects, with sources fingerprinted in this packet.
Their imports are only Mathlib and the latter imports the former. No
arithmetic or prior-proof replay was run. The native source imports
contain no legacy order predicate, bridge, or alternate tree. Each
new module and an independent cap consumer were checked on the pinned
toolchain; the public conclusions use only standard Lean axioms.
No earlier source, human source, or Git worktree was edited. The
archive contains sources and evidence only.

