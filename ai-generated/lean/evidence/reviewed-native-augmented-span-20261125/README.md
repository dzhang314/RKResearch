# Checked generic augmented-span order criterion

Four Lean modules prove a generic exact criterion for the reviewed
`RKResearch.HasOrder`. They are independent of any particular tableau:

| Checked module | Result |
| --- | --- |
| [RootedTreeAugmentedSpan](../../RKCert/ReviewedNative/RootedTreeAugmentedSpan.lean) | Root attachment acts bilinearly on scaled tree features. Graded span closure and vanishing linear order residuals imply `HasOrder` under the coefficient scaling hypotheses. |
| [NativeIntegerSpanClearing](../../RKCert/ReviewedNative/NativeIntegerSpanClearing.lean) | `checkClearing_sound` turns a positive denominator and a verified sparse signed integer identity, including the last coordinate, into rational span membership. |
| [NativeIntegerAugmentedChecker](../../RKCert/ReviewedNative/NativeIntegerAugmentedChecker.lean) | A successful finite integer check of the leaf, matrix actions, all ordered pair clearings and basis payments implies `HasOrder` for the normalized coefficients. The sparse interfaces require agreement with the actual matrix and output products. |
| [NativeIntegerAugmentedTopPay](../../RKCert/ReviewedNative/NativeIntegerAugmentedTopPay.lean) | `hasOrder_of_direct_top_check` allows checking the final degree by direct scalar payments on every ordered split of lower basis rows, with no final-degree basis. It requires the same coefficient and action bindings and a successful check. |

The four typed audits of the [span](../../AuditRootedTreeAugmentedSpan.lean),
[clearing](../../AuditNativeIntegerSpanClearing.lean),
[checker](../../AuditNativeIntegerAugmentedChecker.lean) and
[direct top cut](../../AuditNativeIntegerAugmentedTopPay.lean)
passed on Lean 4.36.0. The
[span](AuditRootedTreeAugmentedSpan.output.txt),
[clearing](AuditNativeIntegerSpanClearing.output.txt),
[checker](AuditNativeIntegerAugmentedChecker.output.txt) and
[top-cut](AuditNativeIntegerAugmentedTopPay.output.txt) outputs contain
eleven axiom reports, each listing only `propext`, `Classical.choice`
and `Quot.sound`.

## Separate arithmetic demonstration

The [27-stage rational order-ten example](../../../upper-bounds/rational/strict-sdirk-order-ten-27/augmented-span/README.md)
checks 404 lower basis-pair memberships, 328 direct order-ten
payments, 95 cached child actions, 95 lower basis payments and the
leaf. The portable Python checker uses the existing tableau without
enumerating trees. **This is exact arithmetic, not a complete Lean
certificate for that tableau.** The generic theorems are checked;
the complete native order-ten instantiation is pending. The published
eleventh tall failure is a separate calculation, not a conclusion
of the generic through-order checker.

## Reproduce

With the archive's pinned Lean 4.36.0 toolchain and Mathlib revision
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842` available, run from
`ai-generated/lean`:

```sh
set -e
receipt=evidence/reviewed-native-augmented-span-20261125
sha256sum -c "$receipt/checked-inputs-and-audit-outputs.sha256"
(cd ../.. && sha256sum -c "ai-generated/lean/$receipt/reviewed-providers.sha256")
lake build +RKCert.ReviewedNative.NativeIntegerAugmentedTopPay
for audit in RootedTreeAugmentedSpan NativeIntegerSpanClearing NativeIntegerAugmentedChecker NativeIntegerAugmentedTopPay; do
  lake env lean -j1 -M1800 -s65536 "Audit$audit.lean"
done
```

The [recorded hashes](checked-inputs-and-audit-outputs.sha256) bind the
four sources, four audit inputs and four outputs. The
[reviewed providers](reviewed-providers.sha256) are unchanged from
archive revision `8071977dd0b979bc39258ffe7960750fd09da807`.
No compiled objects or partial concrete Lean checks are shipped.
