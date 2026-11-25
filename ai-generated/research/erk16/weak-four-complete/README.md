# ERK16: complete physical weak-four exclusion

[The proof](PROOF.md) rules out the actual ordinary four-site arm over every ordered field. The genuine degree-three case is included. In degree four it uses the previously proved [strict-unit-root cut](../weak-four-reductions/02-first-root-count.md), then excludes all remaining clock orders using continuous parameter boxes and the two actually paid first-stop moments. It does not use a fixed physical tableau, a Robin endpoint, a resultant, an additional moment or a diagonal equation.

Run from this directory with standard Python, without optimization:

```sh
python3 check_uniform.py
```

The verifier covers 70 cubic, 168 all-interior quartic, 63 low-exterior and 63 reflected low-exterior rank choices. The four families require 1, 13, 14 and 1 terminal intervals respectively. This is not just a test at finitely many parameter values: every boundary sign is affine in the parameter, and every local two-moment vector is a convex combination of the tested corner vectors throughout its box. The proof explains both steps. To replay the earlier root cut as well, run `python3 ../weak-four-reductions/checks/run_all.py`.

The last section of the proof gives the actual-tableau dispatch, its connection to the separate [weak-five exclusion](../weak-five-complete/PROOF.md), and stage padding. The conclusions here are mathematical; the new scalar exclusions are not presented as end-to-end Lean proofs.
