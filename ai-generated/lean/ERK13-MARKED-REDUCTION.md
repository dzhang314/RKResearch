# Order 13: exact remaining marked-forward charts

This is an internal structural checkpoint, not an order-thirteen stage
bound. The prior full-odd packet removes every nonzero-first-adjoint
Fin19 witness over ordered fields. This follow-on reduces every remaining
19-stage witness to a marked chart with head rank 3 through 5, or an early
pure rank-two marked chart. All tableaux and moments are actual; no
distinct-node, positive-weight, nonzero-weight, or interior-node
hypothesis is imposed.

The checked declaration is
`RKCert.Paired.FiniteMidpoint.order13_fin19_remaining_marked`.
In the rank-two case the terminal coordinate is already an actual
member of `E7`, the core is a physical mask algebra, and the normalized
head is zero on its support. The actual mesh polynomial factors as
`G = P * Q`, with `natDegree Q = 3` and `natDegree P = a - 2`,
where `a=5` in the alias chart and `a=6` otherwise. The representation
`v i = P.eval (nodes A i)` holds at every nonzero head coordinate.

## Proof summary

- Reject both marked degree-eight ghost subspaces using three actual
  affordable consecutive clock shifts; the alias budget spends one extra
  original defect grade. The terminal coordinate belongs to the core by
  numerical localization. The augmented ranks and low products remain
  grades of actual defects plus that one known terminal coordinate.
- If the original fourth-defect rank is three, the marked two-chain
  forces the full augmented fourth defect grade to equal its core.
  The augmented grade-three subspace has codimension one there. Its
  physical incoming primitive observations annihilate that codimension-one
  subspace, so the published three-moment off-mask chronology gives at
  most two off-mask clocks, below the required effective-site count.
- If its original fourth-defect rank is four, local products make the
  augmented core a mask algebra and allow cleaning the head. The actual
  head square has a pure part and one possible marked ghost.
- If terminal entry is early, ordinary fourth defects vanish at the
  terminal; exact terminal stripping normalizes the two scalar moments.
  The adjacent Jacobi recurrences cancel the free coefficient in the
  common-root condition. Coprimality follows from the fixed recurrences
  and the nonzero endpoint values, not from numerical root sampling.
  The no-alias degree-six pencil cannot divide the square of the
  cubic head polynomial: it would be a scalar square with opposite
  leading and midpoint signs. The alias polynomial is separable by an
  exact rational Bézout certificate. The genuine ghost therefore costs
  at most thirteen head plus four core plus one off-head features,
  contradicting the actual full augmented E11 on 19 stages.
- If terminal entry is late, the mesh lifts to the ordinary odd Jacobi
  mesh. If the terminal coordinate entered one grade later, the paid
  grade-four head representation would undo that lift, contradicting its
  nonzero terminal evaluation. The grade-eight ghost thus lifts too
  and is excluded by the full-odd feature bound. In the late pure case
  the exact augmented grade-seven defect cap and existing fixed Jacobi
  Bézout/causal masks give contradiction.
- In the surviving early pure case, the next exact rank forces at
  least eight effective head clocks (nine for alias). The degree
  comparison is therefore a literal polynomial factorization. In alias,
  lowering the degree of Q would make the mesh an actual augmented
  grade-six defect of polynomial degree at most six, violating separation.

## What remains

No order-13 exclusion of Fin19 has been asserted. The outstanding
forward work is the early pure marked rank-two scalar moment gates and
the marked rank-three through rank-five head charts. The audited source
is `pass0045_q6_odd.md` (sections “Completion of every order-13 prefix
case” and “Higher ranks in the prefix”), with
`pass0145_prefix_audit.md` as an independent check. The early no-alias
quartic uses the documented rational resultants of degrees 65 and 100;
lower factors use the companion-exterior capacities, not a fixed
Jacobi divisor gate. The fixed alias quadratic case also needs a
specific checked gate. None of those pending implications is assumed.

## Replay

After the source-only full-odd checkpoint (SHA-256
`e6c57376df60a7e215e483dfe6cb19ae915d20f26d360c67ad9b5a54b9760109`),
add these new sources under `ai-generated/lean/RKCert` and build
`RKCert.ERKOrder13RemainingMarked` on Lean/Mathlib 4.36.0. Re-run
`lake env lean evidence/p13-marked-audit.lean` from the Lean root.
This was verified with the pinned existing cache and leaf-only rebuilds;
no fresh broad Mathlib build or Git operation was used.
