# Lean certificate for the two-tableau DIRK10 portfolio

The [literal portfolio](../dirk10-twelve-field-portfolio/README.md) supplies **12-stage DIRK of exact order ten** over every field of characteristic zero or prime characteristic at least eleven. The kernel also checks the following stronger ring-domain distinctions. None of these statements claims a new stage minimum across all fields.

- **RKResearch.Certified.DIRK10RationalTwelveAlternateFlagReplay.exists_exact_of_unit** certifies the literal alternate tableau over every nontrivial commutative ring inverting its denominator \(D_2\). Integer denominator clearing transports all order conditions, without imposing the additional RREF pivot denominators on the coefficient ring. The two actual next-tree defects and their integer Bézout relation exclude order eleven on the full localization.
- **RKResearch.Certified.DIRK10RationalPortfolio.exists_exact_local** covers every commutative local ring inverting \(10!\), by the integer denominator cover and the local-ring rule for a sum that is a unit.
- **RKResearch.Certified.DIRK10RationalPortfolio.exists_exact_finite_characteristic** covers every nontrivial commutative ring of nonzero characteristic inverting \(10!\). Its proof first checks each prime power, then uses the actual ideal Chinese remainder equivalence, product tableaux, and transfer by ring homomorphisms. It does not assume that the ring itself is local, reduced, or a product of fields.
- **RKResearch.Certified.DIRK10RationalPortfolio.exists_exact_field** checks the stated characteristic-zero and characteristic-at-least-eleven field bound. The stronger **paid_local** and **paid_finite_characteristic** conclusions include a **unit** next-bush defect.

The first tableau is covered by the [previous complete rooted certificate](../dirk10-twelve-native-upper/README.md). The alternate tableau uses the existing **RationalFlagReplay** bridge with exact graded defect flags of ranks \(0,0,0,1,2,4,6,8,9,10\). Evaluations, primitive actions, clock actions and products are checked by the kernel before applying the generic tree recurrence. Its typed audit lists only propext, Classical.choice, and Quot.sound. The numeric coefficient cover, exceptional residues, and Bézout arithmetic have **no axioms** and check in core Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1.

Neither the unit property on individual localizations nor the positive-characteristic CRT result asserts a single witness over an arbitrary characteristic-zero nonlocal ring such as \(\mathbb Z[1/210]\).

## Regenerate and replay

From ai-generated:

    p=research/dirk10-twelve-alternate-native
    tmp=$(mktemp -d)
    python3 -B research/dirk10-twelve-rational-flags/generate-flags.py \
        research/dirk10-twelve-field-portfolio/tableau-alternate.json \
        "$tmp" --stem DIRK10RationalTwelveAlternateFlagReplay
    for f in "$tmp"/*.lean; do cmp "$f" "lean/RKCert/ReviewedNative/$(basename "$f")"; done
    sha256sum -c "$p/sources.sha256"
    sha256sum -c "$p/dependencies.sha256"

From ai-generated/lean (with the matching Mathlib installation):

    lake build +RKCert.ReviewedNative.DIRK10RationalPortfolioFinite
    lake env lean AuditDIRK10RationalPortfolio.lean

The whole alternate/local/finite/field proof and typed audit were checked on pinned Lean/Mathlib **4.36.0**. Only the separate arithmetic module was replayed on all four listed compilers; no other full release pairing is claimed.
