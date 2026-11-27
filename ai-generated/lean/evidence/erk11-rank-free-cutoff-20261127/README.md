# Rank-free first-eleven cutoff checks

Run `lean -j1 RKCert/Research/ERK11RankFreeCutoffGate.lean` from
`ai-generated/lean` on a core Lean toolchain. The four arithmetic and
formal-word receipts pass on 4.34.1, 4.35.0, 4.36.0, and 4.37.0-rc1.
The [paper argument](../../../research/ERK11-RANK-FREE-FIRST-ELEVEN-CUTOFF.md)
uses both shifted order-nine floors to deduce a sharp dense size-six
cutoff in every characteristic-zero 17-stage candidate. It is not an
end-to-end Lean proof, and does not exclude that last extension.
