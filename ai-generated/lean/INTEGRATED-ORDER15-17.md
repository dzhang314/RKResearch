# Three order-15 and order-17 Lean certificates

| Class | Minimum order | Minimum stage count | Coefficients |
|---|---:|---:|---|
| Explicit | 15 | 23 | Any ordered field |
| Explicit | 17 | 27 | Any ordered field |
| Diagonally implicit | 15 | 21 | Any characteristic-zero commutative ring, including fields |

The matrix assumptions are strict lower triangularity for explicit methods and
lower triangularity for diagonally implicit methods. No positivity of weights
or distinctness of abscissae is assumed in these endpoint theorems.

The order-15 explicit façade states its conclusion directly using reviewed
`RKResearch.HasOrder`. The order-17 explicit and order-15 diagonally implicit
certificates still prove their endpoints in the earlier representation.
`AuditIntegratedEndpoints.lean` demonstrates transport from the reviewed
predicate for both of them. These checked transports are not native rebases
of the proof internals.

## Reproduction scope

From `ai-generated/lean`, the named targets and combined consumer are:

```sh
lake build RKCert.ReviewedOrderFifteen RKCert.Dirk15Replay.Final RKCert.ERKOddOrdered17
lake env lean AuditIntegratedEndpoints.lean
```

The named top modules were recompiled from the integrated source on Lean/Mathlib
4.36.0. The checks used an isolated object root containing source-matched
cached dependencies, including the exact previously checked certificates.
Separate consumers and the combined import passed, and the three named top
modules passed targeted kernel replay. The axiom reports contained only
`propext`, `Classical.choice`, and `Quot.sound`. This was not a clean
all-dependency rebuild or a test on any other toolchain.
