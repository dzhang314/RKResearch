module

public import RKCert.ReviewedNative.LocalLinearCleanFourWeights
public import RKCert.ReviewedNative.FiniteOrderedSignWindows

@[expose] public section

/-! # Positive whole-block masses and the origin hull

No sign of any individual output weight is assumed. The cardinal
test pays a strict square on the exact positive degree-19 grid.
The origin hull yields positive weight X, not X(1-X). -/
namespace RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour

open RKResearch Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKCert.ReviewedNative.PositiveRule19 RKCert.ReviewedNative.FiniteOrderedSigns
open scoped Classical Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b τ h W k θ : Fin s → K}
variable {U : Submodule K (Fin s → K)} {S Q : K[X]}

/-- Strict positivity from nonnegative interior values of a nonzero
polynomial, proved by exact sampling rather than ordered-field limits. -/
theorem grid_integral_pos_of_nonzero_nonnegative {l r : K} {G : K[X]}
    (lr : l < r) (nz : G ≠ 0) (deg : G.natDegree < 19)
    (nonneg : ∀ x ∈ Set.Ioo l r, 0 ≤ G.eval x) :
    0 < integral l r G := by
  obtain ⟨i, live⟩ := exists_nonzero_grid_sample lr nz deg
  exact integral_pos_of_grid_samples lr deg.le
    (fun j => nonneg _ (intervalPoint_mem lr j))
    ⟨i, lt_of_le_of_ne (nonneg _ (intervalPoint_mem lr i)) live.symm⟩

/-- Every block mass is positive, even if all but one of its actual
b entries are negative. The test is P times the square of the cardinal
polynomial, of total multiplier degree eleven. -/
theorem UnitFourCompensated.block_mass_pos (B : UnitFourCompensated A b τ W U S Q)
    (ho : HasOrder p A b) (pay : 17 ≤ p)
    (G : UnitCleanFourFeed A b τ h W k θ U (ordinaryProfile Q))
    {x : K} (hx : x ∈ weightedSites (nodes A) θ)
    (paid : indicator (nodes A) θ x ∈ treeSpace A 8) :
    0 < blockMass (nodes A) θ b x := by
  let c := nodes A
  let D := weightedSites c θ
  let P := ordinaryProfile Q
  let L := Lagrange.basis D id x
  have ld : L.natDegree = 3 := by
    have d := Lagrange.natDegree_basis (Set.injOn_id _) hx
    change L.natDegree = D.card-1 at d
    have d4 : D.card = 4 := G.sites
    rw [d4] at d
    exact d
  have lv : L.eval x = 1 := Lagrange.eval_basis_self (Set.injOn_id _) hx
  have ln : L ≠ 0 := by
    intro zero
    rw [zero, eval_zero] at lv
    exact zero_ne_one lv
  let R := P*L^2
  have rd : R.natDegree ≤ 11 :=
    natDegree_mul_le_of_le G.degree (natDegree_pow_le_of_le 2 ld.le)
  have hsum := B.moment_sum ho pay R rd
  rw [sum_by_feed_clock c θ W (fun i wi => (G.support i).mpr wi) R.eval] at hsum
  have fit : blockMass c θ W x = P.eval x * blockMass c θ b x :=
    B.block_mass_fit ho pay G paid
  have single : (∑ z ∈ D, blockMass c θ W z * R.eval z) =
      (P.eval x)^2 * blockMass c θ b x := by
    rw [Finset.sum_eq_single_of_mem x hx]
    · rw [fit]
      simp only [R, eval_mul, eval_pow, lv, one_pow, mul_one]
      ring
    · intro z hz ne
      have ez : L.eval z = 0 := Lagrange.eval_basis_of_ne (v:=id) ne.symm hz
      simp [R, ez]
  have sq : R*P = (P*L)^2 := by
    dsimp only [R]
    ring
  have mass : (P.eval x)^2 * blockMass c θ b x = integral 0 1 ((P*L)^2) := by
    rw [integral_zero_left, formalPrimitive_eq_native, ←sq, ←single]
    exact hsum
  have d8 : (P*L).natDegree ≤ 8 := natDegree_mul_le_of_le G.degree ld.le
  have deg : ((P*L)^2).natDegree < 19 :=
    (natDegree_pow_le_of_le 2 d8).trans_lt (by decide)
  have hpos : 0 < integral 0 1 ((P*L)^2) := by
    refine grid_integral_pos_of_nonzero_nonnegative zero_lt_one
      (pow_ne_zero _ (mul_ne_zero G.live ln)) deg ?_
    intro a _
    simpa only [eval_pow] using sq_nonneg ((P*L).eval a)
  rw [←mass] at hpos
  rcases mul_pos_iff.mp hpos with ⟨_, pos⟩ | ⟨neg, _⟩
  · exact pos
  · exact ((not_lt_of_ge (sq_nonneg (P.eval x))) neg).elim

private theorem nodal_erase_factor (D : Finset K) {x : K} (hx : x ∈ D) :
    nodalHull D = (X-C x)*nodalHull (D.erase x) := by
  unfold nodalHull
  exact (Finset.mul_prod_erase D (fun t => (X-C t : K[X])) hx).symm

/-- A four-clock hull containing the genuine origin pays a strict interior
test for each other clock. This uses the X weight and degree at most 16. -/
theorem nonzero_clock_interior_of_origin_hull {D : Finset K} {P : K[X]}
    (live : P ≠ 0) (pd : P.natDegree ≤ 5) (four : D.card = 4)
    (origin : (0 : K) ∈ D)
    (moments : ∀ R : K[X], R.natDegree ≤ 7 →
      integral 0 1 ((nodalHull D*R)*P) = 0)
    {x : K} (hx : x ∈ D) (xn : x ≠ 0) : 0 < x ∧ x < 1 := by
  let T := (D.erase 0).erase x
  have hx0 : x ∈ D.erase 0 := Finset.mem_erase.mpr ⟨xn, hx⟩
  have t2 : T.card = 2 := by
    change ((D.erase 0).erase x).card = 2
    rw [Finset.card_erase_of_mem hx0, Finset.card_erase_of_mem origin, four] <;> decide
  have fac : nodalHull D = X*((X-C x)*nodalHull T) := by
    rw [nodal_erase_factor D origin, map_zero, sub_zero, nodal_erase_factor (D.erase 0) hx0]
  let L := P*nodalHull T
  have ld : L.natDegree ≤ 7 :=
    natDegree_mul_le_of_le pd ((natDegree_nodalHull T).trans t2).le
  have ln : L ≠ 0 := mul_ne_zero live (monic_nodalHull T).ne_zero
  let V : K[X] := X*(X-C x)*L^2
  have vd : V.natDegree < 19 :=
    (natDegree_mul_le_of_le (natDegree_mul_le_of_le natDegree_X.le (natDegree_X_sub_C x).le)
      (natDegree_pow_le_of_le 2 ld)).trans_lt (by decide)
  have vn : V ≠ 0 := mul_ne_zero (mul_ne_zero X_ne_zero (X_sub_C_ne_zero x))
    (pow_ne_zero _ ln)
  have z0 : integral 0 1 V = 0 := by
    have eq : (nodalHull D*L)*P = V := by
      rw [fac]
      dsimp only [V, L]
      ring
    simpa only [eq] using moments L ld
  constructor
  · by_contra bad
    have nonneg : ∀ a ∈ Set.Ioo (0 : K) 1, 0 ≤ V.eval a := by
      intro a ha
      have hit : 0 ≤ a-x := sub_nonneg.mpr ((le_of_not_gt bad).trans ha.1.le)
      have vsgn := mul_nonneg (mul_nonneg ha.1.le hit) (sq_nonneg (L.eval a))
      simpa only [V, eval_mul, eval_X, eval_sub, eval_C, eval_pow] using vsgn
    exact (grid_integral_pos_of_nonzero_nonnegative zero_lt_one vn vd nonneg).ne' z0
  · by_contra bad
    have nonneg : ∀ a ∈ Set.Ioo (0 : K) 1, 0 ≤ (-V).eval a := by
      intro a ha
      have hit : a-x ≤ 0 := sub_nonpos.mpr (ha.2.le.trans (le_of_not_gt bad))
      have vsgn := mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos ha.1.le hit) (sq_nonneg (L.eval a))
      simpa only [V, eval_neg, eval_mul, eval_X, eval_sub, eval_C, eval_pow] using
        neg_nonneg.mpr vsgn
    have z : integral 0 1 (-V) = 0 := by rw [map_neg, z0, neg_zero]
    exact (grid_integral_pos_of_nonzero_nonnegative zero_lt_one (neg_ne_zero.mpr vn)
      (by simpa only [natDegree_neg] using vd) nonneg).ne' z

theorem UnitFourCompensated.nonzero_clock_interior (B : UnitFourCompensated A b τ W U S Q)
    (ho : HasOrder p A b) (pay : 17 ≤ p)
    (G : UnitCleanFourFeed A b τ h W k θ U (ordinaryProfile Q))
    (origin : (0 : K) ∈ weightedSites (nodes A) θ)
    {x : K} (hx : x ∈ weightedSites (nodes A) θ) (xn : x ≠ 0) :
    0 < x ∧ x < 1 :=
  nonzero_clock_interior_of_origin_hull G.live G.degree G.sites origin
    (B.hull_moment ho pay G) hx xn

end
end RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour
