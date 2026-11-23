# Runge–Kutta certificates in Lean

**Theorem.** If a strictly lower-triangular `s`-stage tableau satisfies every rooted-tree order condition through `p`, then `p ≤ s`. For the classical four-stage rational tableau, Lean also proves that every condition through order four holds, and that order five is impossible.

These are exact, algebraic statements about the Butcher coefficients. They are not analytic theorems about convergence for differential equations, and they do not establish any of the stronger research bounds in the surrounding archive.

## What Lean checks

| File | Result |
| --- | --- |
| [`RKCert/Tree.lean`](RKCert/Tree.lean) | Defines rooted trees, their order and tree factorial `γ`, and elementary RK weights `Φ`. The chain with `n` edges has `n+1` vertices and factorial `(n+1)!`. |
| [`RKCert/Field.lean`](RKCert/Field.lean) | Over any characteristic-zero field, `γ(t) Φ(t) = 1` is equivalent to `Φ(t) = 1/γ(t)`. |
| [`RKCert/StageBound.lean`](RKCert/StageBound.lean) | `explicit_order_le_stages`: after `n` applications of `A`, the first `n` components vanish. For `n=s`, the chain condition would require `0=1`. The proof even works over any nontrivial commutative semiring for the denominator-cleared conditions. |
| [`RKCert/Enumeration.lean`](RKCert/Enumeration.lean) | An exact finite checker for a specified tableau; a theorem proves its list contains precisely all trees with at most `p` vertices. |
| [`RKCert/RK4.lean`](RKCert/RK4.lean) | Exact order four of the classical tableau over `ℚ`, using the complete tree checker and the general stage bound. |
| [`RKCert/Regression.lean`](RKCert/Regression.lean) | Negative control: a three-stage explicit tableau satisfies all chain tests through degree three but fails the two-leaf fork (`1/2` rather than `1/3`). |

`Tree.attach c r` adds `c` as a child of the root of `r`. This is an ordered representation: permuting siblings creates multiple representatives of the same unordered tree, not additional classical conditions. The weights multiply child factors in a commutative ring. The finite list through order four has nine ordered representatives (eight unordered trees). A chain has stage vector `Aⁿ 1`; this conclusion is derived from the same recursion as the branched cases. Stage indices in Lean are zero-based. The count includes the empty, zero-stage case.

## Reproduce

From this directory, with a Lean toolchain manager (`elan`) and Git installed:

```sh
lean --version                     # Lean 4.36.0
lake exe cache get Mathlib.Algebra.BigOperators.Ring.Finset Mathlib.Data.Nat.Factorial.Basic Mathlib.Data.Fintype.Basic Mathlib.Data.Fintype.Fin Mathlib.Algebra.Field.Rat Mathlib.Algebra.CharZero.Defs
lake build
lake env lean Audit.lean
```

The cache step only downloads Mathlib's compiled dependencies; it is optional if building them from source. `lean-toolchain` and `lake-manifest.json` pin the toolchain and dependency revisions. The project's only direct Lake dependency is Mathlib v4.36.0. The source contains no admitted proofs, user-supplied axioms, or native-evaluation proof shortcuts. `Audit.lean` prints the transitive axiom dependencies of the named certificates.
