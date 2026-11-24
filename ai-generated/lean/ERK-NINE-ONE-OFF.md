# ERK order nine: checked one-off reductions

Import `RKCert.ERKOrderNineOneOffStructure`. This is an additive
source-only packet, not the full ERK order-nine 13-stage lower bound.
It does not edit or recompute an earlier good-prime tape.

## Scope

- `RKCert.Paired.OneOff.order9_amplitude_fork` concerns an actual strict
  12-stage order-nine tableau with exactly one defect-support abscissa over
  any characteristic-zero field. It derives the initial nonzero clock,
  the exact two-dimensional defect span, the quadratic defect form, and
  the first nonzero (Ag) feature in its actual chronological location.
  The dependent-square case proves constant amplitude globally and
  forces this first feature on; the independent-square case derives its
  corrected defect basis and exact cubic/matrix relations.
- `RKCert.Paired.OneOff.order8_amplitude_fork` gives the same guarded result
  for an actual order-eight 10-stage tableau. Neither remaining p8 branch
  is thereby excluded.
- `RKCert.Paired.order9_forbid_same_clock_interpolation` is the actual
  rank-ten causal obstruction. If the evaluation rows before a stage are
  independent on grade four, no interpolation on grade five by earlier
  rows at that same clock is possible. It does not merge or identify
  states merely sharing an abscissa.
- `RKCert.Paired.OneOff.endpoint_jacobi_three_roots_impossible` is the exact
  rational endpoint test from the recovered one-off manuscript. It works
  over all characteristic-zero fields, with the distinct endpoint roots,
  the Jacobi polynomial identity and the slope polynomial explicitly in
  the hypotheses.
- `RKCert.Paired.OneOff.order9_tail_cubic_impossible` and
  `RKCert.Paired.OneOff.order9_tail_quartic_impossible` concern actual
  order-nine tree moments over any ordered field. They respectively
  exclude the cubic and quartic beta pencil alternatives **once the
  physical tail identity or identities and endpoint root restrictions
  are supplied**. The old H48 branch instead excludes five-off/six-on and
  leaves only the one-off case. These new theorems do not yet discharge
  all of the one-off case.

## Exact arithmetic and Mathlib reuse

The manuscript, `Runge_Kutta_Shorter_Proofs_and_Stronger_Bounds.txt`,
lines 1773–2633, contains the initial amplitude cases, prefix, endpoint
and terminal argument. Its original endpoint script also occurs in the
historical replay. For its only finite modular calculation in this
branch, a smaller integral certificate suffices:

    U(d,z) (F(d,z)-E(d))/(z-d) + V(d,z) G(d,z) + W(d,z) E(d)=631060.

Here the division denotes the explicitly checked exact polynomial
quotient, not an unchecked operation. The 54 nonzero coefficients of
the three witnesses have at most 12 decimal digits. Two signed
coefficient-grid equalities are checked by ordinary kernel reduction
`of_decide_eq_true rfl` using the existing verified `GoodPrimeDense`
coefficient evaluator. The nonzero integer and Jacobi determinant
bridge are also checked. The optional Python generator is not trusted;
no new native proof axiom or large resultant object is needed.

The ordered terminal proof is algebraic. The exact formal
(x(1-x)) integral of a nonzero square is positive by the existing
shifted Cauchy Gram and affine substitution. In the quartic case,
write the monic polynomial as (Q L), where (Q) accounts for the
two known fibres. The degree-two (L) is not assumed to split.
A putative nontrivial null vector of the 2×2 moment form produces
an affine polynomial (f). Reduce (Q T f) modulo (Q L);
the remainder is (Q V) of degree at most three. A further reduction
of polynomial tests modulo (L) and the paid orthogonality give
vanishing beta integral of its square. Positivity forces it to be
zero, so coprimality and degree give the contradiction. The cubic
case similarly uses its known linear complement, obtaining a
nonzero mass by positivity of the square of the known fibre divisor.
Both proofs reuse the actual reflected moment budget. No auxiliary
root splitting, real closure, analytic integration, or positive RK
output weight is assumed.

Mathlib APIs reused include native linear factors and coprimality,
`Polynomial.modByMonic_add_div`, `natDegree_modByMonic_lt`,
`natDegree_divByMonic`, `Monic.eq_X_add_C`,
`mul_dvd_mul_iff_left`, `IsCoprime.dvd_of_dvd_mul_left`,
`Submodule.finrank_sup_span_singleton`, and `LinearMap`/polynomial
coefficient algebra. Causal row support and the precise tree-order
budget are RK-specific.

## Remaining physical work

1. Close both independent-square branches after the verified
   `independent_square_shape`: calibrate the first new corrected
   amplitude feature and discharge the ordinary and exceptional
   (d=a/2) and (d=2a) geometries. A reusable prefix shortcut is
   to apply (A) to the exact interpolation identity
   (h=h_d, c(c-a)/(d(d-a))+
   [h_v/(v-u_0)](g-u_0, c(d-c)/(a(d-a)))) on the four known source
   features, and to (c^3-(a+d)c^2+ad,c). This avoids repeated
   separate incoming coefficient solves, but is not asserted in
   this packet for those two branches.
2. Derive the global normal form and (gh=0); obtain the actual
   five-row prefix by genuine identical-row merges only, prove
   maximality of the grade-five/grade-six spaces and produce
   the sixth and seventh features.
3. Establish the exact seventh-row compatibility identities and
   the physical eighth/ninth action equations. Then apply the verified
   endpoint and terminal leaves. The endpoint nondegeneracy and
   terminal moment algebra are no longer open scalar calculations.

## Build and inputs

The receipt uses pinned Lean 4.36.0 commit
`611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`, Mathlib commit
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, additive named leaves only.
No compatibility claim for earlier versions is made. Shared sources
are identified in `BASE_IMPORTS.sha256`; the existing chart and
good-prime source packets remain unchanged. The local ordered Gram
predecessor was byte-identical to its published source. The expected
integration is after the sealed p9 physical chart and exact H48
support packet, with the published ordered Gram modules present.

All 14 new named modules, including the umbrella, compiled. Eleven exported
statements passed the standard axiom audit. The independent umbrella
replay hit its 56-second wall timeout under shared load (no theorem
diagnostic); no full clean or duplicate umbrella replay was attempted.
The separate exact endpoint replay receipt is in `replay-light.log`.

The direct boundary comparison to published `b083e10` is in
`PUBLISHED_BOUNDARY_COMPARISON.tsv`. Eight shared direct sources are
byte-identical; `ERKLowEndpointCore` and `ERKLowLobatto` differ only
in existing proof bodies by explicit `coeff_monomial` simp arguments
for version portability. Their statements and definitions are unchanged.
`ERKGoodPrimeDense` is from the exact H48 support packet, not the
published baseline. The verified old source hashes are recorded
separately from the latest published hashes. Do not replace published
proof bodies when integrating this additive archive.
