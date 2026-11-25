# Algebraicity of the exact literal SDIRK(11,8) witness

The Lean theorem proves existence over ℝ. This separate mathematical argument shows that the same literal tableau is defined over a real algebraic extension of degree at most 12. The degree bound is not formalized in Lean.

## Field tower

Fix the standard monomial basis and any real triple `s,t,c` supplied by the literal scalar proof. Use the ordered subfields F₀ = ℚ, F₁ = ℚ(s), F₂ = F₁(t), F₃ = F₂(c) of ℝ.

1. `sRoot` is the monic cubic s³ − 9s² + 18s − 6 = 0 over F₀, so [F₁:F₀] ≤ 3.
2. `tRoot` is the monic quadratic t² − (s+3)t + s = 0 over F₁, so [F₂:F₁] ≤ 2.
3. Over F₂ let z = (1+s)/2 + s and Z = (X−(1+s)/2)(X−s)(X−t)(X−1). Each of the four μⱼ is the finite sum z⁻¹ Σₙ [Xⁿ](Xʲ Z)·zⁿ⁺¹/(n+1), with 0 ≤ n ≤ j+4. This equals `avg M z (X^j * Zpoly s t)` for the standard powers. Therefore `beta0`, `beta1` belong to F₂. `cRoot` is the monic polynomial c² + β₁c + β₀ = 0 over F₂, so [F₃:F₂] ≤ 2.

By the tower law [F₃:ℚ] ≤ 3·2·2 = 12. That is an upper bound, not an irreducibility or precise degree claim. `bStar = -beta1 - c` is already in F₃. For E(T) = `affineAt M s t c T`, `dAt = -E(0)/(E(1)-E(0))` is also in F₃: calibration selects no additional root.

## Why these are the actual emitted coefficients

For any intermediate field F ⊆ ℝ containing s,t,c, use the predicates “scalar in F,” “vector entrywise in F,” and “polynomial coefficientwise in F.” The only potentially non-obvious closures are the scalar primitive and evaluation. When P = Σₙ pₙXⁿ, the standard-basis constructors are I(P) = Σₙ (pₙ/(n+1))Xⁿ⁺¹ and Eₓ(P) = Σₙ pₙxⁿ, with finite coefficient support; `avg` is E_z(I(P))/z and `mean` is E₁(I(P)). Thus I preserves F[X] and evaluation/averaging have values in F at nodes in F. The exact formulas follow from polynomial expansion, linearity and `primitive_pow`, `eval_pow`; the coefficient legs also appear in `SDIRK118ScalarExistence`. The noncomputable `M.constr` is not a hidden choice of coefficients: `standardPowers M` determines these maps.

The formulas used to form the tableau are in the following Lean modules:

- `SDIRK118ExactScalarDonorBinding`: `avg`, μ, `beta0/1`, `ellAvg`, `selectorQuadAt`, `affineAt` and `dAt` use these operations. Consequently γ = z⁻¹, the six sites and each `card6` weight are in F. The four `HF/KR` are normalized or straightened finite products with coefficients in F; their construction uses `atOne` and the actual `clean` covector.
- `SDIRK118ForwardProjection`, lines 64–222, and `SDIRK118ReverseOperator`: the three cardinal coefficient vectors use explicit field quotients. `polyProject` is `toPoly` of `interp - along defectCoef (interp c g)`, with `defectCoef` the reciprocal pivot times the fourth-site residual. Thus both projections map F⁴ into F[X] and use no matrix inverse chosen by existence. The forward fourth tap uses the explicit moments and `gdAt`, the reverse fourth uses `shiftAt` on that interpolation. The first three normalized rows, all evaluation maps, and both matrices `G`, `R` preserve subfield membership.
- `SDIRK118LiteralAssembly`: the literal three pairings/taps `t40`, `t50`, `t54` are finite dot products divided by weights, then `targetRows` and `revRows` act by addition, composition and field arithmetic. `matrixOf` probes the operator on the 0/1 coordinate vectors, so its entries belong to F whenever the operator preserves membership. The suffix is entrywise (wⱼ/wᵢ)Lⱼᵢ. The cross operator is (Eₓ I − T Eₓ)Πf. This gives every entry of the block tableau, the split weights and γ.
- `SDIRK118LiteralClaimPin`: fixed `finSumFinEquiv` only changes indices. `contractMatrix 4 2` selects each retained row and uses `mergeCoefficient 4 2` on its columns; the same operation on b adds the relevant deleted weight. These maps only select entries and add the deleted contribution. Hence the conclusion is about the same explicit A₁₁,b₁₁ and γ returned by the real endpoint, not an arbitrary real existential witness.

## Denominator scopes (no new sign argument)

- Root coefficients: the sole moment pivot Dμ in `beta0`, `beta1` is nonzero by `seed.momentPivotPos`. Normalization at z uses `literal_z_pos`. Division by a natural successor in I is over ℚ.
- Calibration: `affineAt` has the geometric denominators 1−r, a−r, 1−a for r=s/3 and a=(1+s)/2; their nonvanishing follows from the exact s placement. The denominator E(1)−E(0) defining d is nonzero by the already proved exact affine identity and the opposite endpoint signs at 15/4 and 4. This is distinct from evaluating E or finding a new root.
- Normalized rows/projections: the common-row denominator h−2, the positive η in `Vd`, `Ld` in `gdAt`, and the tilts `(a-1)*g0`, `(a-1)*g1` are the existing forward scalar/placement guards. Cardinal denominators are differences at distinct old sites. `defectCoef` uses the actual separate forward and reverse interpolation pivots, bound in the forward/reverse producer proofs; neither pivot is a new entry in `ExactScalarSeed`.
- Weights and cut polynomials: `atOne` for each HF/KR and `card6` use distinct-site products; `straighten` divides by `clean ru`. The latter is exactly the `ResidualPivot` exported by `literal_residual_pivot`, via the existing determinant, residual J₀ guard, and explicit probe, not an additional nonzero assumption on the final witness. Tap divisions are only W₄ and W₅. The weighted transpose uses the nonzero split masses, supplied by `literal_scalar_leaves`/`ScalarMasses` from the four old guards and the exterior-mass determinant identity.
- Algebraicity alone does not require these guards anew. They justify the geometric interpretation and the established real formulas. For Lean subfield closure, all operations are total and 0⁻¹ = 0, so the literal membership lemma can be proved without any nonvanishing or sign premise.

Taking F = F₃ proves that every actual real coefficient is algebraic over ℚ, independently of whether the order theorem has been closed. A real order proof on the same seed and formula yields the combined statement.
