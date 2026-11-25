# Last-active reflected origin transport

The [Lean theorem](../../RKCert/ReviewedNative/EndpointOriginTransport.lean)
works over an arbitrary field with the original strictly explicit stage
order and the original last nonzero weight at stage `t`. The reflected
clock is zero at `t` exactly when the first adjoint seed vanishes at
`t`, and exactly when the actual paired or primitive reverse flag
vanishes there. These equivalences do not require the first seed to
vanish globally, an order payment, or a sign condition on the weights.
The corresponding equivalence for a general credit sequence takes
tail-vanishing credits through the grade in question.

If the actual reverse flag equals the annihilator of a forward space
`V`, origin is equivalent to membership of the physical coordinate
column `e_t` in `V`. Inclusion in that annihilator suffices for the
membership-to-origin implication. With the reviewed `HasOrder p`
predicate, that implication applies to `treeSpace A j` once
`j + 2 ≤ p` is paid. The result does not supply saturation, coordinate
membership, or an unconditional stage lower bound.

The exact body and separate [typed audit](../../RKCert/ReviewedNative/EndpointOriginTransportAudit.lean)
both exited zero under Lean 4.36.0 and the pinned Mathlib revision.
The audit used the measured body and emitted no compiled artifacts.
It elaborated nine typed clients covering the seven equivalences and
two one-way corollaries. The [raw report](typed-audit-output.txt)
contains only the standard axiom dependencies `propext`,
`Classical.choice`, and `Quot.sound`, as recorded in the
[axiom table](actual-axioms.tsv). The [acceptance ledger](acceptance.tsv)
and [14 reviewed provider source hashes](reviewed-providers.sha256)
record the measured cut. No compiled artifacts are included.

For an independent source check with the pinned dependencies already
available, run from `ai-generated/lean`:

```sh
lake build +RKCert.ReviewedNative.EndpointOriginTransport:olean
lake env lean RKCert/ReviewedNative/EndpointOriginTransportAudit.lean
```
