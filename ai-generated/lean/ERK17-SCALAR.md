# ERK17 scalar cut on native proof inputs

All new canonical sources are under `ai-generated/lean/RKCert/ReviewedNative/`.
The target reviewed input is `91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5`.
Nothing here converts a tree, tableau or order theorem. This is not an
unconditional bound on the number of stages.

## Pick the earliest usable geometry output

Write Jₘ for (−1)ᵐ times the derivative of Mathlib's integer shifted Legendre
polynomial of degree m, mapped to the coefficient field. Write I for the formal
primitive with constant term zero. All scalar statements work over every
characteristic-zero field; the stage argument for ordered fields remains separate.

1. **Normalized pencil.** `no_pencil_ports` refutes exactly seven scalar facts:
   deg P=5; u≠0; P(u)≠0; (J₉+aJ₈)(u)=0; P divides J₉+aJ₈;
   I(XP)(u)=I(X²P)(u)=0. The two local moments are separate equations.
   There is no restriction u∈[0,1], no monicity requirement on P, and no
   requirement that the divisor split.
2. **Earlier, before choosing a pencil.** `no_mesh_ports` refutes a polynomial
   P of degree at most five and a nonzero cofactor N of degree at most three,
   with N(u)=0, the same nonzero omitted clock and local equations, and the
   seven consecutive unit moment differences for M=XPN:
   I(XᵏM)(1)=I(Xᵏ⁺¹M)(1), 0≤k≤6. The cofactor need not be monic, separable,
   or given by explicitly factored roots. P≠0 already follows from P(u)≠0.
3. **Actual small-support quadrature.** `MeshPorts.of_quadrature` produces
   the previous data from any finite signed quadrature exact through degree ten
   for the weight (1−X)P: I(R(1−X)P)(1)=Σᵢ R(cᵢ)wᵢ. Nonzero-weight clocks
   must lie in {0}∪S with |S|≤3, u∈S. The same degree bound on P, u≠0,
   P(u)≠0 and two local zero moments must be supplied. Choose
   N=∏_{z∈S}(X−z). No positivity, distinct physical rows, or genuine origin
   atom is required. Tests R=XᵏXN annihilate every active row and have
   degree at most 10. The independent consumer uses cᵢ=(A·1)ᵢ on a genuine
   reviewed-shaped matrix with 26 rows, but **assumes** the geometric data.

## Shared with ERK15

`RKCert.ReviewedNative.JacobiMomentPorts` consists only of the signed slope
and moment condition, with imports of Mathlib and the pure `NodalPrimitive`.
`RKCert.ReviewedNative.ERK17ScalarPorts` is likewise safe for geometry to
import without pulling in any legacy order or replay implementation.

`RKCert.ReviewedNative.JacobiMomentBand` is independent of the ERK17 replay.
Its public `JacobiMoments.signedSlope_band` says: deg D≤r+2 and r+1 moment
differences on XD put D in span{J_{r+3},J_{r+2}}. This converts monomial
tests by linearity, reuses the characteristic-zero Jacobi top-two lemma
and a nonzero change of normalization. ERK17 uses r=6; the ERK15 marked
degree-seven pencil can use r=5. The smoke consumer instantiates both. No
mesh matrix, Legendre recurrence or determinant is reconstructed.

`RKCert.ReviewedNative.ERK17ScalarFromReplay` handles the lower fixed
coefficient case by the frozen Lobatto-8 first-moment exclusion. If the
higher coefficient is nonzero, the degree-eight free pencil forces deg P=5
and the excluded two-moment certificate is the exact existing
`RKCert.ERK17Norm.Pair` through `odd_pencil_impossible_of_pair`. The private
backend still imports geometry transitively; no such geometry proposition
or tableau is consumed in these proofs. No heavy replay object is changed.

## What is still open

On the original strict tableau, derive the width-26 reduction, handle the
nonzero backward seed, and, on the zero-seed branch, produce the actual
rank/four-port geometry (including the origin-free branch when applicable).
The first nonzero active clock must really have the two local primitive
zeros. A list of polynomial roots, a numerical search, or the old stage
theorem is not a substitute. The reviewed native primitive identity
`RKResearch.Certified.Graded.formalPrimitive_eq_native` from
`RKCert.ReviewedNative.ForwardNodalGain` connects existing geometry without
any legacy order conversion; this interface does not import it.

## Verification

Run `python3 checks/run_small.py` from this staged Lean tree on the preserved
source-matched cache used by `rk-legacy-single-root-verify`. It validates the
source bytes of the required RK closure, uses a single local object root, and
only compiles and separately kernel-replays the four named small modules.
The audit imports the exact reviewed `RKResearch.OrderConditions`. Build
details and SHA-256 values are in `checks/receipt.json`; no full determinant
or whole-archive rebuild is claimed.
