# Order-six field dependence and checked lower bounds

`SDIRKSix163.exists_exact` is a literal six-stage strict SDIRK witness of exact order six over the field of size 163. `HasOrder.common_diagonal_order_six_stages_universal` proves six is the sharp uniform floor over nontrivial commutative rings. The four-constant theorem proves seven whenever the explicit cast product is nonnilpotent (also whenever the diagonal is a nonunit).

The ten integral coefficient combinations are the existing checked combinations, now used before scalar cancellation. A monic projection cancels the twelve-branch multiplier over the coefficient ring before specializing; the physical forward/reverse proof pays for all small denominators directly from order six.

All five modules were compiled and independently replayed with Lean 4.36.0 and Mathlib 4.36.0 (Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`). The twelve named statements in the axiom report use only the standard Lean axioms. The alternate finite-field checker takes the path to `F163.json`.
