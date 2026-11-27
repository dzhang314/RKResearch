# First-excess effect of a genuinely paid null perturbation

`RKResearch.Certified.TwoDonorDense.null_perturbation_firstExcess`
checks that appending a stage with a shifted dense receiver plus a
physical covector that kills every lower paid rooted column leaves
the new stage pure through the corresponding lower grade. At the
next grade the only possible extra term is the exact unary read
of that physical covector, with the normalized child's size factor.
The theorem uses the reviewed rooted derivative definitions.
Lean 4.36.0 with matching Mathlib passed the separate typed import
with standard axioms only. The real algebraic instance is replayed
in the [new stem note](../../../research/real-sdirk15-movable-port/README.md);
no full native algebraic tableau theorem is claimed.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/sdirk15-movable-port-20261127/sources.sha256
lake build RKCert.ReviewedNative.MovablePurePort
lake env lean -j1 evidence/sdirk15-movable-port-20261127/AuditMovable.lean
```
