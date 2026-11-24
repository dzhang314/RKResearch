# Finite ERK midpoints: structural Lean certificate

Pinned Lean 4.36.0 and Mathlib v4.36.0. From this directory run `lake build RKCert.ERKFiniteStaircase`, followed by
`lake env lean ERKFiniteMidpointAudit.lean`.

This is a structural checkpoint, **not a proof of the stage floors 24, 26, 27, 29**.
The full order is `2*q+ε`, with `8≤q`, `ε≤1`, and no restriction on signs, zero
weights or repeated nodes. A putative tableau of at most `3*q+2*ε-1` physical
stages has exact midpoint ranks, a live last weight, and the actual normalized
one-head representation. The midpoint F escape uses the published incoming
Hermite gain directly; no additional low-order stage bound or special
invariant-completion theorem is needed.

* `RKCert.Paired.FiniteMidpoint.saturated`: exact s, F_j for 5≤j≤q, E_q and E_(q−1), and seed rank cap.
* `midpoint_noninvariant` and `head_chart`: F_j clock escape for 5≤j≤q and the true one-head flag with r≥2.
* `margin`: unified even, odd live reverse seed and odd zero reverse seed cases. The last-coordinate ideal is present precisely when rank(back 0)=0 at odd order; it is stable under diagonal multiplication and A kills it. Gives all marked E caps, exact marked E_q/E_(q−1) ranks, and reverse annihilation of the marker.
* `even_terminal_column`, `even_last_zero`: terminal c=1, coordinate vector in E_q and F_q zero there for the even case.
* `RKCert.Paired.ReverseHull.reverse_primitive_annih_six` and `three_failed_of_five_moments`: exact reflected polynomial primitive pay through degree five, and a degree-two knot annihilator certificate giving three distinct nonzero failed blocks.
* `finite_reverse_gain`, `edge_noninvariant`, `band_staircase`: the marked reverse dimension refund removes clock invariance at E_q by +3 and after E_q by +2, once the relevant adjacent E ranks are paid. The extended band is propagated through E_(p−3) conditional on the explicit initial paid-band equality and its rank. This is not yet an assertion that every actual tableau supplies that equality.

The remaining work is proof of the finite polynomial/midpoint intersection in the
three parity charts (including odd prefix alias), the H10 leakage removal, the
actual cleaned profile and physical contrast extraction, and the connections to
the published fixed/free knot gates. The scalar gates already published are not
reproved here. The archive has no axiom placeholders, no native decision or
external numerical search.
