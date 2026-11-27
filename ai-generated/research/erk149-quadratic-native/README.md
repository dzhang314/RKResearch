# Kernel-checked 14-stage ERK of exact order nine

This packet is the kernel replay of the [six-opening, two-pair quadratic tableau](../../upper-bounds/real-algebraic/erk14-order9-six-opening-two-pair/README.md), not a claim that order ten is attained in fourteen stages. Its coefficients are of the form \((a+b\sqrt{15})/863280633600\) with integer \(a,b\). The order-nine theorem holds over any commutative ring containing a square root of \(15\) and an inverse for the denominator; no ordering or positivity hypothesis enters it. The displayed real instance is strictly lower triangular and fails the actual size-ten tree obtained by attaching the root of one five-vertex bush as a child of the root of another. Its scaled order defect on that tree is \(1/3456\).

The memo stores 486 canonical rooted-tree keys, all joins staying within order nine, and all 200 stage-action vectors through size eight. The soundness module routes the existing binary-tree order definition through the canonical joins, then transports integer pair arithmetic by the square-root and inverse identities. The finite key, join, action and payment checks are all proved by kernel reduction, not by native code execution or an external oracle. The audit prints the generic order theorem, exact failure and real witness with only propext, Classical.choice, and Quot.sound.

From the repository root, regenerate and compare the literal Lean data with:

    folder=ai-generated/research/erk149-quadratic-native
    fixture=ai-generated/upper-bounds/real-algebraic/erk14-order9-six-opening-two-pair/positive.json
    out=$(mktemp)
    python3 "$folder/generate_memo.py" "$fixture" "$out"
    cmp "$out" ai-generated/lean/RKCert/ReviewedNative/ERK149QuadraticMemoData.lean
    rm "$out"

The input fixture has SHA-256 d8ea047d140f168a72fea3f1a85fab78ef99271d84f97f60f95872d3aa0eb8b3.

In the prepared Mathlib project at ai-generated/lean, build the chain from the data through the final checks and run the typed audit:

    lake build +RKCert.ReviewedNative.ERK149QuadraticMemoChecks
    lake env lean AuditERK149QuadraticMemo.lean

Tested with Lean/Mathlib 4.36.0. This Mathlib-dependent module has not been tested against other release-matched Mathlib installations.
