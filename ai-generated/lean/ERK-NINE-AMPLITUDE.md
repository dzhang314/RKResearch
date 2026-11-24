# Complete one-off amplitude exclusion and global normal form

This additive packet is part of the existing ERK order-nine (and reusable
order-eight) lower-bound proof. It does not yet exclude the final one-off
tableau or promote either numerical bound.

Import `RKCert.ERKOrderNineOneOffCleanClocks`.

- `independent_square_on_first_impossible` and
  `independent_square_off_first_impossible` close both independent-square
  cases of the manuscript on actual chronological stage vectors. Their
  antecedent ranks are exactly the physical rank chart, not fabricated
  scalar data. The exceptions a=2d and d=2a are excluded by the first new
  clean clock and its exact C(4) constraints, not by dividing out those
  possible factors.
- `order9_constant_amplitude` proves the genuine sole-off constant
  amplitude for a strict 12-stage p9 tableau over any characteristic-zero
  field. `order8_constant_amplitude` gives the same result on a strict
  10-stage p8 tableau. The cancellation concerns aggregate off weight,
  not any individual output coefficient.
- `order9_global_normal` and `order8_global_normal` prove the entire
  global one-off normal form over those fields. In the notation g=qdef,
  h=Ag and C=diag(c), the checked equations include Ah=(dI−C)h and the
  exact cubic defect with h coefficient (2d²−2a²)/a and Ch coefficient
  −d/a. The fourth homogeneous defect space is the span of g,h,Ch.
- `first_doubled_clean_clock` places the first nonzero (C−dI)h on 2d,
  with exact h=a d². `new_clean_clock_h` finds a distinct clean clock
  outside {0,d,2d} with nonzero h, using the exact cleanClockTest identity.
  Neither conclusion assigns a physical numbered stage by assumption.

The only new calculations are short exact row identities for the already
documented proof. They replace repeated small Vandermonde solves by
causal action on explicit polynomial combinations of actual source
features. All conditions used to divide are proved at their respective
chronological innovations. The final clean-clock resultant is a direct
combination of two scaled polynomial residuals. Repeated features are
not identified or merged. No new search, native proof axiom, or
computation on unchecked numerical root data is used.

## Remaining physical bridge

The main p9 proof still needs g h=0, actual first numbered rows and
rank-five maximization, seventh-row identities and placement, and
eighth/ninth tail construction. The prior packet already checks the
endpoint Jacobi nondegeneracy and conditional terminal contradictions.
p8 still requires its remaining one-off and four-off exclusions.

## Pinned verification

Lean 4.36.0 at commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`,
Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Every new
named leaf was compiled individually with existing imported objects.
Shared CPU/I/O caused a few early short wall timeouts; their serial
named retries completed, without a full rebuild. See the exact
audit and leaf receipts in this packet. This does not claim an older
toolchain build.

Prerequisite: the previously sealed `rk-erk-order9-one-off-reductions-delta-20261124.zip`
(SHA-256 `491ad9a5e5f951da469b804f2b75065c25819b18accf32a2852c06fa746a7b23`)
on its earlier physical chart and checked H48 support. New sources leave
all previously sealed files unchanged; there are no compiled objects
in the archive.
