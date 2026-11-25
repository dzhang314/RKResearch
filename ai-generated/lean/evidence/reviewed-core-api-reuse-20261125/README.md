# Reuse of reviewed coefficient maps and quadrature units

Four AI-side modules now call the reviewed theorems for applying a coefficient homomorphism to tree weights, preserving and reflecting order, and obtaining a unit from a paid quadrature moment. Their public statements and callers are unchanged. The normalization proofs that need scalar homogeneity and cancellation remain in place.

Lean/Mathlib 4.36.0 compiled and separately kernel-replayed each modified module. The five named checks use only the standard Lean axioms. The previously published native order-17 endpoint also compiled and kernel-replayed with the revised modules on the checked dependency bank. This is a targeted recheck, not a rebuild of all previously reported certificates.
