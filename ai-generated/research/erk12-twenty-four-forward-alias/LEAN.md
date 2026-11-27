# Lean kernel certificate for the 24-stage tableau

The public endpoint module is RKCert.ReviewedNative.ERK12UniversalTwentyFour.

- RKResearch.Certified.ERK12UniversalTwentyFour.order_twelve proves
  HasOrder 12 for the literal tableau with its common scale inverted.
- RKResearch.Certified.ERK12UniversalTwentyFour.exists_exact constructs
  a strict explicit 24-stage tableau of order twelve, not thirteen,
  in any nontrivial commutative ring where \(12!\) is a unit.
- RKResearch.Certified.ERK12UniversalTwentyFour.exists_exact_iff_factorial_unit
  records exactly the required coefficient-ring condition for existence
  at this width. It does not claim 24 is minimal.

The certificate uses the existing integer rooted-tree Gram machinery,
so no full tree enumeration or trusted external computation is part of
the Lean proof. Each covariance has 25 coordinates, the 24 stage
coordinates and one carrying the degree scale. At each grade the
kernel rechecks the two sparse factored matrix products, the exact
covariance update, and the zero output energy. The reviewed
Gram theorem turns the zero sum of integer squares into the exact
integer order equations for every rooted tree. Only the integer
certificate uses the order on integers; the equations transfer to an
arbitrary commutative coefficient ring where the scale is a unit.
After content removal the largest covariance entry has 140 decimal
digits. The two rooted-tree failures and their integer unit combination
are checked separately.

From ai-generated/lean, use the pinned Mathlib and Lean 4.36.0:

    lake build +RKCert.ReviewedNative.ERK12UniversalTwentyFour:olean

With dependencies already compiled, recheck only the public endpoint:

    lake env lean --root=. RKCert/ReviewedNative/ERK12UniversalTwentyFour.lean

The kernel reports the axiom sets in lean-4.36-audit.txt. No Lean
version other than 4.36.0 is reported as checked in this packet.

To regenerate the finite covariance and check shards from the
literal tableau, from ai-generated:

    python3 -B research/erk12-twenty-four-forward-alias/generate_gram.py \
      --emit lean/RKCert/ReviewedNative --modules /tmp/erk12-24-modules.txt
    sha256sum -c research/erk12-twenty-four-forward-alias/lean-sha256.txt

The sparse core and public endpoint are handwritten and are not
overwritten by the generator.
