# Rational contributing quadrature support

- [Four-shift lower bound and proof](proof.md): at least
  \(\min(17,p-3)\) contributing rational sites for quadrature order
  \(p\ge4\), including 16 at order 19 and 17 at order 20.
  Weights are arbitrary in a characteristic-zero field; repeated
  nodes are grouped and only nonzero aggregate sites count.
  The proof applies to the reviewed RK bushy moments without
  assuming triangularity. It is not an additional unrestricted stage
  bound or a Lean-certified result.
- [Standalone 19-site quadrature of exact order 20](standalone-19.md):
  all weights are positive and all sites are interior and rational.
  This is an exact quadrature witness, not an RK stage upper bound.
- [Runge–Kutta donor realization](../quadrature-donor-realization/realization.md):
  every paid scalar rule lifts with the same contributing sites and
  weights. The exact \(u/128\) rule above gives 19 contributing sites in
  209 physical rows at exact RK order 20, with no stage-bound
  improvement. The proof and checker do not claim a Lean certificate.
- [Earlier odd-prime projection and exact finite pencil certificates](../rational-quadrature-prime-cut/prime-cut.md):
  retained in full. The four-shift formula agrees with the archived
  endpoint at orders 8–10 and improves it at orders 11–20. The archived
  stronger lower bounds at orders 6 (four sites) and 7 (five sites)
  are not superseded.
- [Checked four-site lower bound at order five](../strict-sdirk-rational/order-five-rational-support-lean.md):
  remains stronger there than the uniform four-shift formula.

Replay the finite residue evidence with `python3 verify-four-shift.py`
([expected output](exact-check.txt)) and separately replay the positive
rule with `python3 verify-standalone-19.py`
([expected output](standalone-19-check.txt)). Both use Python's standard
library and exact arithmetic, with no Lean invocation or search.
