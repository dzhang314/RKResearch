# Actual DIRK two-port invisibility without a local exception

The Lean entry point is [`RKCert.DirkEvenJointSupport`](RKCert/DirkEvenJointSupport.lean), checked with Lean and Mathlib v4.36.0. Its reusable weighted four-debut argument also applies to other lower triangular tableaux.

**What changed.** The original unrestricted lower triangular tableau at p=2m, s=3m−3, m≥7 cannot have a reflected-clock-invariant one-dimensional cubic reverse line. Killing the last physical pivot of that line directly on the native transpose produces a causal linear operation with generally signed, possibly vanishing weights. It is not assumed to be an RK method. The weighted four-debut proof obtains the physical stages from true scalar quadrature, obtains all pivot refunds and weights on these rows, accounts for all zero-weight/repeated coordinate constraints in the common input/output cut, and invokes the existing scalar fourth-debut Bézout. No order or conjugation on the field is required.

**Unconditional original-array conclusions.** F3 is killed coordinatewise by both original weight b and true reverse cubic τ at all these even boundaries. The same holds on F_j whenever 4≤j and 2j+1≤m; and F4 is killed at p16/s21 even though that count does not pay the entire Jacobi family. Any vector vanishing at the origin and on both ports belongs to F_{m−1}. In particular a noninitial **physical coordinate** exists where b and τ both vanish and its single-stage cardinal is in F_{m−1}. This does not permit removing its stage and is not a standalone proof of p16≥22.

Scope: arbitrary characteristic-zero fields. The local invariant hypothesis from the preceding DIRK nonlocal port release is conclusively removed here, not just replaced by a different branch assumption.
