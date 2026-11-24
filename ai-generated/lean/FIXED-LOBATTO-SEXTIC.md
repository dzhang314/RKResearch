# The five-omitted-knot order-20 scalar gate

Let K be any characteristic-zero field, D=(X−1)X L′₁₀ the closed
shifted-Legendre polynomial in the project's native normalization,
and let a₁,…,a₅,u be six distinct roots of D in K, with u nonzero.
If deg Q≤6, Q(aᵢ)=0 for all five, and the formal zero-constant
primitives of XQ and X²Q vanish at u, then Q=0. The old roots are
allowed to contain 0 or 1. There is no positivity, ordering, monicity
of Q, real-root assumption, or projection of a tableau. This theorem
supplies only the e=6 branch of a separately paid order-20 boundary;
it gives no new numerical stage floor by itself.

Write T=∏(X−aᵢ). Distinctness and the five original zero evaluations
give T∣Q. A nonzero sextic would have Q=T(A+BX). Write cᵢ for the
coefficient of Xⁱ in T and for k=1,2,3 define the integer polynomial
Mₖ=Σᵢ(2520/(k+i+1))cᵢ uⁱ. Every divisor appearing divides 2520.
The normalized primitive identity is
2520 J[XᵏT](u)=u^(k+1) Mₖ. Thus the two paid observations put the
column (A,uB) in the nullspace of the two-by-two Hankel matrix with
first row (M₁,M₂) and second row (M₂,M₃). It suffices to prove its
minor M₁M₃−M₂² is nonzero. We cancel powers of u only in the actual
characteristic-zero chart, where u≠0 is assumed. The *normalized*
minor is an integer polynomial in all six knots, meaningful also
when the residue of u is zero.

Scale each knot by 16796. They are roots of the previously verified
monic, degree-11 integral polynomial integral10. The minor is
homogeneous of degree 10 under simultaneous scaling, by the native
coefficient formula for Polynomial.scaleRoots. At the split prime
15727 the entire scaled grid has distinct residues
0, 1069, 1186, 6796, 7356, 7876, 8398, 8920, 9440, 10000, 15610.
Take all 462 five-element sublists and each of the six remaining
pivots: 2772 normalized determinants. All are nonzero, by explicit
Lean kernel reduction in 42 small chunks. Permutation of the first
five knots does not change their nodal polynomial; subset coverage
is obtained via Mathlib's nodup, subpermutation and sublistsLen.
An independent standard-library integer replay yields product
3388 modulo 15727. That product is a reproducibility checksum;
the Lean proof establishes each inequality, rather than assuming
the checksum or external program.

The general split-prime root-tuple theorem puts the six scaled
integral knots in the integral closure and selects a residue field
above 15727. Simplicity of the reduced grid preserves all required
pairwise inequalities under specialization; the grid splits already
over its prime field. Any zero minor in K would therefore give a
zero in the exact checked table. This does not reduce Q or any
unknown tableau parameters modulo a prime. Returning to K,
the determinant kills A and uB, hence A and B, so Q=0.

Entry points: RKCert.Sextic.lobatto10_minor (no nonzero-pivot
hypothesis for the normalized minor), RKCert.Sextic.lobatto10_five_omitted
(original zero primitives require the sixth knot to be nonzero).

## Pinned Mathlib reuse decisions

Use Polynomial.coeff_scaleRoots, Polynomial.mul_scaleRoots_of_noZeroDivisors
and Polynomial.X_sub_C_scaleRoots as-is. The local row_scale and
scale_product lemmas adapt those identities to the project-specific
cleared rows and root lists, without redefining root scaling. Use
Polynomial.dvd_iff_isRoot and Polynomial.natDegree_mul as-is for
division by the five roots; the short list induction keeps the exact
ordered factor that the executable coefficient recurrence consumes.
For combinatorial coverage use List.nodup_ofFn, List.subperm_of_subset
and List.mem_sublistsLen as-is, not a new normalization or sorting
algorithm. Reuse the existing fixed grid, its squarefree prime
specialization, and the project's formal primitive identities as-is.
Only the normalized degree-five minor, its integer Horner evaluator,
and the table itself are instance-specific. The Horner evaluator is
proved equal to the mathematical minor over any commutative ring.
