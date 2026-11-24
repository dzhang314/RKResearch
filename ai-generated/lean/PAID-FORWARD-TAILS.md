# When paid forward polynomial tails must vanish

**Status:** proved with stable Lean and Mathlib v4.36.0. These are scalar
theorems over any characteristic-zero field, not numerical evidence or
new unconditional Runge–Kutta stage minima. The tableau argument still
has to produce the closed grid, the indicated endpoint roots and low
moments for its actual tails, and the displayed congruences.

Write J(F)=∫₀¹ F for the formal primitive evaluated at 1,
μ_j(H)=J(XʲH), and D_m=(X−1) lobatto(m), where the latter factor is the
project's signed X times the derivative of Mathlib's shifted Legendre
polynomial. A (m,q)-paid tail has degree at most m, is zero at 0 and 1,
and has μ₀ through μ_q zero, inclusive. The integral here is algebraic;
the field need not be ordered or embed in the reals.

## Core proofs

1. **Two clean endpoints save a moment.** If H has degree at most m,
   H(0)=H(1)=0 and μ_j(H)=0 for j+2≤m, then H=0. First J(H′)=0.
   For 1≤r≤m−1, both endpoints of XʳH are zero, so the product rule
   and the fundamental theorem for formal primitives give
   μ_r(H′)=−r μ_{r−1}(H)=0. The derivative has degree at most m−1.
   The previously proved, characteristic-zero shifted-Hilbert detector
   at the nonzero endpoint 1 (shift 0) forces H′=0; the zero constant
   term then forces H=0. There is no argument by squares or positivity.
2. **The grid pays all multiples through degree 2m−1.** The degree of
   D_m is exactly m+1 whenever m>0, from Mathlib's shifted Legendre
   degree, the characteristic-zero derivative degree, and injective
   coefficient extension. For m=7,8,9,10 the checked closed-grid
   orthogonality is J(D_m V)=0 for deg V≤m−2. Consequently if D_m
   divides R of degree at most 2m−1, J(R)=0.
3. **Links.** For tails of degree at most m, if D_m divides XH₀−H₁,
   applying point 2 to Xᵏ(XH₀−H₁) gives μ_{k+1}(H₀)=μ_k(H₁) for
   k≤m−2. Thus a tail with vanishing zeroth moment inherits a
   following tail's entire paid prefix, shifted up by one. If H₀=0,
   then D_m divides H₁, which is impossible for nonzero H₁ of
   degree at most m.
4. **A short annihilating factor.** Suppose deg H≤m, *either* clean
   endpoint holds, μ₀,…,μ_q vanish, and D_m divides QH with Q nonzero
   of degree d≤q+1. Induct on n<m to show μ_n(H)=0. For an unpaid n,
   write k=n−d; J(XᵏQH)=0 by point 2, since k+d+m≤2m−1.
   Expanding Q gives a sum of Q_i μ_{k+i}(H). All terms except the
   leading one vanish by induction. Its coefficient is nonzero, so
   μ_n(H)=0 as well. The one-endpoint moment detector from the
   existing quadrature theory now yields H=0. No root of Q needs to
   be found, and no degree-of-product equality is assumed when H=0.

## Exact consequences used by the order-14 / order-16 charts

* At m=7, if H₀,H₁,H₂ are (7,3)-paid tails and
  D₇ divides both XH₀−H₁ and XH₁−H₂, then all three vanish. The two
  links pay through moment 5, precisely enough by the two endpoints.
* At m=8, if H₀,H₁ are (8,5)-paid tails and D₈ divides XH₀−H₁,
  both vanish. A single link pays moment 6.
* For m=7,8 a linear annihilating factor X−a suffices for the standard
  (m,2m−11)-paid tail. More generally any nonzero factor of degree at
  most 4 (m=7) or 6 (m=8) suffices. In particular the order-16
  singleton case only needs the weaker bound three. These conclusions
  concern an annihilator modulo D_m, not a claimed irreducibility
  or a factor of the method coefficients.

## Lean and Mathlib

The namespace is `RKCert.Paired.Terminal`. The three import-ordered
leaves are `EndpointTailMoments`, `LobattoTailRecurrence`, and
`LobattoPaidTails`. Public conclusions:
`two_endpoint_moment_detect`, `closed_lobatto_small_factor_detect`,
`lobatto_tail_linear`, `lobatto7_tail_two_links`,
`lobatto8_tail_one_link`, and `lobatto8_tail_short_factor`. The
one-step prefix and forward zero propagation are exposed directly by
`LobattoPaidTail.extend_of_link` and `LobattoPaidTail.eq_zero_of_prev`.

Reused as-is from Mathlib: `Polynomial.natDegree_shiftedLegendre`,
`Polynomial.natDegree_derivative`, `Polynomial.derivative_ne_zero`,
`Polynomial.natDegree_map_eq_of_injective`, `Polynomial.as_sum_range`,
the product rule, and linear-map and finite-sum identities. The RK
library supplies its exact formal primitive, shifted-Hilbert detector,
and `Terminal.closed_lobatto_orthogonal` / `endpoint_moment_detect`.
The new lemmas connect these established components; there is no
second polynomial/integral type, determinant computation, or manually
entered coefficient table.
