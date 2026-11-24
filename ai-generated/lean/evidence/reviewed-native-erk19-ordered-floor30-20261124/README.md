# Order nineteen requires thirty explicit stages

`RKResearch.Certified.ERK19.ordered_erk19_stage_floor30` states that a strictly explicit tableau satisfying the reviewed order conditions through order 19 has at least 30 stages over any ordered field. There is no assumption on the signs of the weights, the first reverse seed, or the numerical order of the stage clocks.

Zero padding first reduces the theorem to ruling out exactly 29 stages. The proof splits on the actual first reverse seed of that tableau. The [nonzero case](../reviewed-native-erk19-nonzero-20261124/README.md) is already checked. If the seed is zero, the [native adapter](../ordered-window-adapters-20261124/README.md) supplies moments at four actual chronological clocks. Absorbing exterior factors into the positive integration weight budgets the clocks outside the unit interval. The opposed forward and reverse moments then force more sign alternations than the degree of the quintic allows.

The [mathematical proof of the zero-seed case](../../../lower-bounds/conditional/erk_order19_zero_first_seed_opposed_windows_20261124.md) explains the sign changes. The formal argument uses exact positive rational quadrature, polynomial operations and inequality proofs over the original ordered field; no real-closed-field or root-existence assumption is used. The published bound itself is unchanged; this certificate reaches it without a seed or scalar hypothesis.

Five modules are listed in rebuild order, including the separate conditional increasing-window exclusion at order 16. Each passed an independent named kernel replay on Lean 4.36.0 with the matching Mathlib. Three audit sources check typed statements and run seven standard-axiom queries. No other version was checked in this pass.
