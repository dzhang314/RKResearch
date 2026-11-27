# Lean certificate: the alternative thirteen-stage rational DIRK

This kernel-checked certificate covers the [literal two-port tableau](../dirk10-thirteen-rational-two-ports/README.md), not the sharper [twelve-stage rational result](../dirk10-twelve-native-upper/README.md). The two tableaux have different denominators and can specialize to different positive characteristics.

In **RKResearch.Certified.DIRK10RationalThirteen**, **order_ten** and **bush_defect** apply directly to the literal thirteen-stage tableau over every commutative ring inverting \(D=126767366286331069785024000\). **exists_exact_of_unit** concludes lower triangularity, order ten and not order eleven for each **nontrivial** such ring. **exists_exact_charZero** and **exists_exact_rational** give the field and rational statements. The [typed audit](typed-4.36.0.log) lists only propext, Classical.choice, and Quot.sound. The Gram data are independently checked by the kernel.

From ai-generated:

    dir=research/dirk10-thirteen-native-upper
    tmp=$(mktemp -d)
    python3 -B "$dir/generate_lean.py" research/dirk10-thirteen-rational-two-ports/tableau.json --graded > "$tmp/DIRK10RationalThirteenGram.lean"
    cmp "$tmp/DIRK10RationalThirteenGram.lean" lean/RKCert/ReviewedNative/DIRK10RationalThirteenGram.lean
    sha256sum -c "$dir/sources.sha256"

From ai-generated/lean in the pinned environment:

    lake build +RKCert.ReviewedNative.DIRK10RationalThirteen
    lake env lean AuditDIRK10RationalThirteen.lean

Direct source builds and the audit passed with Lean/Mathlib **4.36.0**. Other release-matched Mathlib versions are not asserted by this receipt.
