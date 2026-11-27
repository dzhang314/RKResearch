# Lean kernel verification

The endpoint is RKCert.ReviewedNative.ERK11UniversalTwentyTwo.

- RKResearch.Certified.ERK11UniversalTwentyTwo.order_eleven proves HasOrder 11
  for the literal tableau over any commutative ring in which its common
  denominator has the specified inverse.
- RKResearch.Certified.ERK11UniversalTwentyTwo.exists_exact gives a strictly
  explicit 22-stage order-eleven, not order-twelve tableau over every
  nontrivial commutative ring in which \(11!\) is a unit.
- RKResearch.Certified.ERK11UniversalTwentyTwo.exists_exact_iff_factorial_unit
  gives the corresponding existence equivalence on exactly 22 stages.
  The reverse implication is an existence result, not a minimum-stage
  claim. The forward implication reads the order-eleven tall tree.

The Lean table contains scaled integer coefficients at common denominator
\(D=941072888448000\). The untrusted generator enumerates 1,803 distinct
normalized integer stage vectors, partitioned by grade as
\(1,1,2,4,8,16,35,78,182,432,1044\). The kernel checks the root, 759
matrix actions, 3,544 vector join transitions, grade coverage, and
all 1,803 scaled output equations. The reviewed generic binary
rooted-tree recurrence converts those identities into HasOrder 11 for
every tree; the proof does not ask Lean to trust the enumerator. Sparse
integer actions use verified support lists. The order-twelve test checks
the specified tree and integer identity separately and transfers the
unit obstruction to the coefficient ring.

Replay from ai-generated/lean (pinned Mathlib):

    lake build +RKCert.ReviewedNative.ERK11UniversalTwentyTwo:olean

The olean target keeps the check at the elaboration/kernel level. With
its dependencies already compiled, recheck just the public endpoint and
see its axiom output directly:

    lake env lean --root=. RKCert/ReviewedNative/ERK11UniversalTwentyTwo.lean

The kernel outputs for the three public endpoints are in
lean-4.36-audit.txt. Only Lean 4.36.0 has been checked for this
packet. The source uses standard kernel decidability proofs, not
native_decide or compiler reduction axioms.

The checked integer shards can be regenerated in place from the
literal tableau. From ai-generated:

    python3 -B research/erk11-twenty-two-shared-origin/generate_lean.py \
      --emit lean/RKCert/ReviewedNative --modules /tmp/erk11-22-modules.txt
    sha256sum -c research/erk11-twenty-two-shared-origin/lean-sha256.txt

The core, join-slice adapter, and public endpoint are handwritten;
the generator does not overwrite them.
