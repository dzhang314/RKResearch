# Native explicit stage floor with the grade-five surplus

Every order-p strictly lower triangular Runge–Kutta tableau over a **characteristic-zero commutative ring** with p≥10 has at least

```text
⌈3p/2⌉ − 1 = ((3*p+1)/2)-1
```

original stages. The field and ring entry points are
`RKResearch.HasOrder.erk_grade_five_charZero_stages_field` and
`RKResearch.HasOrder.erk_grade_five_charZero_stages`. The existing arbitrary-ring floor is unchanged.

The independent tests give 14, 16, 17 and 19 stages at orders 10, 11, 12 and 13 respectively. The 17-stage result at order 12 is the **general grade-five bound**, not the separate strongest 18-stage order-12 certificate. No logarithmic/doubling improvement or order-specific geometry is claimed.

## Reusable proof join

- The published `grade_five_surplus_of_reviewed_order` proves `dim F₅ ≥ 5` for native strict order p≥10 over a characteristic-zero field.
- `erk_rank_interval_of_coeff_sep` and `erk_paid_rank_interval` propagate the actual rank of an earlier positive grade a to any later paid midpoint q. Strict inclusions come from the original separated stage algebra, so `dim F_q ≥ dim F_a + (q-a)`. The clock separation at the even cutoff uses a real zero first row; no order 2q+1 is borrowed.
- `erk_count_of_midpoint_rank` works over **every field**. It translates `floor(p/2)+extra ≤ dim F_floor(p/2)` into `⌈3p/2⌉−1+extra ≤ s` for p≥4. It consumes the reviewed even/odd physical midpoint budgets. It can incorporate any later proved surplus without importing its proof.
- `HasOrder.strict_lower_triangular_of_charZero_fields` preserves both the human order and strict lower triangularity (including the diagonal) under the existing prime-disjoint coefficient specialization. No domain, reducedness, additive torsion-free or chosen-map hypothesis is imposed on the ring. The independent example includes the ring ℚ × ZMod 2.

## Verified against the human snapshot

The human definitions are from `91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5`; no old order predicate, tree or conversion enters the dependency chain. The canonical native input archive for the grade-five surplus has SHA-256 `d316335a4022bb38880e2b0b3c6e2d985fb624f88def5af746c74b613df263f8`; the native uniform midpoint delta has SHA-256 `71c76c64974af0d4175f71662b6014f09e346101754b7639325dc10dde76e879`. The grade-five surplus module also exposes a previously reviewed order-15 forward-head corollary; neither that corollary nor a new order-15/17 theorem is used here. The only differently named local imports in that previously reviewed closure are the tree-free algebra modules OneEscape, NodalPrimitive, and NodalHermiteRank.

Verified with cached Lean/Mathlib 4.36.0 (Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`): scoped module compile, independent arbitrary-field/ring consumer, and kernel replay of the new module only. Axiom checks show only `propext`, `Classical.choice`, and `Quot.sound`. Source fingerprints for the full local proof closure are in `source-inputs.sha256`. No heavyweight arithmetic was rerun.

With the verified native prerequisites in the pinned `ai-generated/lean` package:

```sh
lake build RKCert.ReviewedNative.ERKCharZero
lake env lean AuditReviewedNativeERKCharZero.lean
lake env leanchecker --verbose RKCert.ReviewedNative.ERKCharZero
```
