# Exact order-nine strict SDIRK over the rationals, in 23 stages

[The checked existence theorem](../../RKCert/ReviewedNative/RationalStrictSDIRKTwentyThreeStageNineUpper.lean)
gives a rational lower-triangular tableau on 23 stages with common nonzero
diagonal `1/9`. For this same tableau it proves the reviewed `HasOrder 9 A b`
and `¬ HasOrder 10 A b`. The tenth tall-tree weight is
`672263002006281827534440264169/2489086143060781104997013158963200000`,
not `1/3628800`. This is a rational upper witness, not a stage minimum
or a stability claim.

The [literal coefficients](../../RKCert/ReviewedNative/RationalStrictSDIRKTwentyThreeStageNineData.lean)
reuse an 11-row zero-weight core. The [checked lists](complete-native-grades.tsv)
cover all 2,056 ordered presentations of rooted trees through order nine,
representing 486 unordered tree shapes. The
[independent arithmetic checker](check_exact_table.py) reads the same
Lean literals without a second coefficient table; its
[output](exact-arithmetic-replay.json) is not used by the Lean proof.

## Lean replay

The archive records the [exact project input hashes](input.sources.sha256),
[five reviewed provider hashes](reviewed-providers.sha256),
and [topological replay order](replay-order.tsv). The checked run used
[Lean 4.36.0](toolchain.txt) and Mathlib revision
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The final theorem and
standalone [typed audit](../../AuditReviewedRationalStrictSDIRKTwentyThreeStageNineUpper.lean)
both exited successfully; see the [terminal receipt](terminal.txt) and
[final replay status](final-replay.tsv). All four [axiom reports](audit-output.txt)
list only `propext`, `Classical.choice`, and `Quot.sound`.

From `ai-generated/lean`, in a build workspace using the pinned toolchain:

```sh
receipt=evidence/reviewed-native-rational-sdirk-twenty-three-stage-nine-20261125
sha256sum -c "$receipt/input.sources.sha256"
(cd ../.. && sha256sum -c "ai-generated/lean/$receipt/reviewed-providers.sha256")
lake build +RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineUpper
lake env lean -j1 -M1800 -s65536 AuditReviewedRationalStrictSDIRKTwentyThreeStageNineUpper.lean
```

The checked run processed modules serially. In a memory-constrained
workspace, build module targets in the recorded order before running the
standalone last audit. No compiled objects are shipped.
