# Order 13: complete nonzero-first-adjoint exclusion

**Scope.** This is a fully checked structural theorem for actual 19-stage
explicit order-13 Runge–Kutta tableaux over arbitrary ordered fields. It
does not yet prove a 20-stage bound. The remaining case is the marked
prefix where the first reflected adjoint vanishes. No new Git or external
actions were performed.

## Checked theorems

`RKCert.Paired.FiniteMidpoint.order13_fin19_zero_first_adjoint`: a strictly
lower tableau of actual order 13 on `Fin 19` satisfies
`backSeed1 A b = 0`, i.e. the exact physical identity
`Aᵀ b = diag (1 - c) b` where `c = A 1`.

`RKCert.Paired.FiniteMidpoint.order13_fin19_prefix_and_full_eleven`: the
same tableau has terminal clock 1 and `treePlus A 1 11 = ⊤`. Here
`treePlus A 1 11` adds only the terminal coordinate line to the true
rooted-tree column space through grade eleven. The proof allows repeated
clocks, exterior abscissae, and arbitrary signed or zero weights.

## Proof and exact dependencies

1. The actual midpoint budget gives the full-odd chart when the first
   adjoint is nonzero. The inherited chart has genuine defect space
   `F7 = U + w P_(r+1)(c)`. This uses the ordered Hilbert Gram, not
   positivity of tableau quadrature weights. Two consecutive true
   grade-eight shifts kill the sole (x J_5) leakage.
2. `dim F4` equals 3 or 4 and the head length `r` lies in 2 through 5.
   For `dim F4 = 4` and `r >= 3`, mask-local products and actual square
   shifts give the degree-at-most-three multiplier. The paid 3+2 primitive
   masks, reused from the checked order-fourteen work, rule it out.
   For `dim F4 = 3` and `r = 2`, the published three-mask chronology
   gives at most five effective clocks, fewer than the required seven.
3. The remaining low ranks have a joint-block profile
   (v w-P(C)w\in U), with genuine (v\in F_3), nonzero (P) of degree
   at most 3, and (U) invariant under (C) and multiplication by (v).
   The profiles follow from the true head square or paid short shifts.
   The p12 joint-mask pipeline supplies an earliest mismatch block. At
   that block every pure grade-seven chain member restricts to the core.
   The first detecting value of (v) itself is necessarily zero there.
   This yields the same exact 3+2 tests, without any root-factor
   assumptions for these profiles.
4. For `dim F4 = 4, r = 2`, the pure case with eight or more head sites
   is excluded by an exact rational Bézout certificate in the actual
   full-odd Jacobi polynomial. In a genuine ghost the explicit eliminant
   (Phi=G^2-G Q R-H Q^2) has degree at most fourteen. Two heads at the
   same clock use a double zero; one multiplicity is always wasted at
   zero. Thus at most thirteen head, three core, and one off-head
   feature remain. In the remaining narrow pure branch there are at most
   seven head, three core and seven off-head features.
5. Exact rank seventeen of E10 forces exactly seventeen earlier
   representatives. Literal aggregation preserves actual order 11 and
   every branched top order-12 tree. The original reflected primitives
   transfer directly by testing v and Av where both are class-constant,
   not by assuming a projected reverse hull. A single causal row repair
   completes order 12 if the first residual vanishes at the greatest
   active weight. Otherwise the actual compressed rank chart supplies
   the one-, two- and three-power spans of that residual. With
   (h=(1-c)b) and (g=(\alpha/2)d), the equations are exactly the
   previously checked p12 two-node chronology, contradicted by
   actual order-11 reflected quadrature capacity. This excludes the
   tied tableau without a split-prime inference or an unproved unary
   order condition.
6. The sole possible margin is now the zero-adjoint marked prefix.
   Its terminal clock is 1. The checked reverse chart forces augmented
   E11 to be the entire stage space. Forward exclusion of that marked
   prefix is a separate and still open formalization.

## Replay

Pinned Lean and Mathlib v4.36.0 only. In a compatible source tree, add
the files beneath `ai-generated/lean/RKCert/` from this source-only
checkpoint, then run the RKCert package build for `RKCert.ERKOrder13FullOdd`
and `lake env lean p13-full-odd-audit.lean` from its Lean root. The
hash ledger records dependencies against the 2e95eb7-compatible base,
including any order-fourteen pieces that this branch reuses and that the
base does not yet contain. Never replace an already published byte-identical
file. The local leaf replay used the existing pinned Mathlib and project
olean caches and did not rebuild a duplicate full dependency closure.
