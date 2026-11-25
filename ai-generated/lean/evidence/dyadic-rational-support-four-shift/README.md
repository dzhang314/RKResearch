# A Lean lower bound on contributing rational abscissae

[The Lean proof](../../RKCert/ReviewedNative/DyadicRationalSupportFourShift.lean)
checks the four-shift lower bound in the reviewed order conditions.
In any characteristic-zero field, if every contributing abscissa is
rational, an order-`p` tableau has at least `min 17 (p − 3)` distinct
contributing sites. Repeated nodes are grouped and zero aggregate
weights are discarded. The weights themselves may be arbitrary in the
coefficient field; no triangularity or sign assumptions are needed.

At order 20 the resulting lower bound is 17. The proof neither excludes
17 sites nor certifies the separate 18-site construction. It is not a
new unrestricted RK stage bound.

The [named audit](../../AuditDyadicRationalSupportFourShift.lean) checks
the exact theorem types; all ten [raw axiom reports](typed-axiom-audit.log)
list only `propext`, `Classical.choice` and `Quot.sound`. The
[dependency hashes](dependencies.sha256) cover the exact accepted
project sources. The successful build used Lean 4.36.0 and Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.

From the repository root:

```sh
sha256sum -c ai-generated/lean/evidence/dyadic-rational-support-four-shift/dependencies.sha256
cd ai-generated/lean
lake build +RKCert.ReviewedNative.DyadicRationalSupportFourShift
lake env lean -j1 -M3000 AuditDyadicRationalSupportFourShift.lean
```
