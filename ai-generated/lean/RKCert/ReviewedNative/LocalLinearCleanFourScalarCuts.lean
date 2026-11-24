module

public import RKCert.ReviewedNative.LocalLinearCleanFourChronology
public import RKCert.ReviewedNative.LocalLinearCleanFourMassHull
public import RKCert.ReviewedNative.OpposedThreePivot
public import RKCert.ReviewedNative.OriginFactorFourThree

@[expose] public section

/-! # Chronological scalar cuts for a clean four-clock feed

All filters are on the first physical row of a complete clock block.
The forward weight is X when the origin is present. The reverse weight
is 1, not 1-X. The scalar theorem handles every numerical pivot order.
Without the origin the first two actual blocks pay the rooted 4+3 cut. -/
namespace RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour

open RKResearch Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKCert.ReviewedNative.PositiveRule19 RKCert.ReviewedNative.FiniteOrderedSigns
open RKCert.ReviewedNative.Quintic
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] {s n p m : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b τ h W k θ : Fin s → K}
variable {U : Submodule K (Fin s → K)} {P S Q : K[X]}

set_option maxRecDepth 4000
set_option maxHeartbeats 950000

section Forward
variable [CharZero K]

theorem FeedChronology.forward_primitive_zero (E : FeedChronology (nodes A) θ m)
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder p A b) (pay : 17 ≤ p)
    (G : UnitCleanFourFeed A b τ h W k θ U P)
    (inside : hiddenKernel b τ U ≤ zeroSpace A 8)
    (stable : (hiddenKernel b τ U).map (diag (nodes A)) ≤ hiddenKernel b τ U)
    (i : Fin m) (R : K[X]) (rd : R.natDegree ≤ 3)
    (masked : ∀ j, j < i → R.eval (E.clock j) = 0) :
    (primitive (R*P)).eval (E.clock i) = 0 := by
  refine forward_mask_zero ha ho pay G inside stable (E.site i) R rd ?_
  intro z hz before
  obtain ⟨j, rfl⟩ := E.covers z hz
  exact masked j (E.ordered.lt_iff_lt.mp before)

theorem FeedChronology.forward_interval_zero (E : FeedChronology (nodes A) θ m)
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder p A b) (pay : 17 ≤ p)
    (G : UnitCleanFourFeed A b τ h W k θ U P)
    (inside : hiddenKernel b τ U ≤ zeroSpace A 8)
    (stable : (hiddenKernel b τ U).map (diag (nodes A)) ≤ hiddenKernel b τ U)
    (i : Fin m) (R : K[X]) (rd : R.natDegree ≤ 3)
    (masked : ∀ j, j < i → R.eval (E.clock j) = 0) :
    integral 0 (E.clock i) (R*P) = 0 := by
  rw [integral_zero_left, formalPrimitive_eq_native]
  exact E.forward_primitive_zero ha ho pay G inside stable i R rd masked

end Forward

private theorem before_one {i : Fin 4} (h : i < 1) : i = 0 := by
  have v : i.val < 1 := h
  apply Fin.ext
  change i.val = 0
  omega

private theorem before_two {i : Fin 4} (h : i < 2) : i = 0 ∨ i = 1 := by
  have v : i.val < 2 := h
  have which : i.val = 0 ∨ i.val = 1 := by omega
  exact which.imp Fin.ext Fin.ext

private theorem before_three {i : Fin 4} (h : i < 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  have v : i.val < 3 := h
  have which : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  exact which.imp Fin.ext (Or.imp Fin.ext Fin.ext)

private theorem after_one {i : Fin 4} (h : 1 < i) : i = 2 ∨ i = 3 := by
  have v : 1 < i.val := h
  have lt := i.isLt
  have which : i.val = 2 ∨ i.val = 3 := by omega
  exact which.imp Fin.ext Fin.ext

private theorem after_two {i : Fin 4} (h : 2 < i) : i = 3 := by
  have v : 2 < i.val := h
  have lt := i.isLt
  apply Fin.ext
  change i.val = 3
  omega

private theorem no_after_three {i : Fin 4} (h : 3 < i) : False := by
  have v : 3 < i.val := h
  have lt := i.isLt
  omega

private theorem monomial_degree_le {d : ℕ} (j : Fin (d+1)) :
    ((X : K[X])^j.val).natDegree ≤ d := by
  rw [natDegree_X_pow]
  exact Nat.le_of_lt_succ j.isLt

section NoOrigin
variable [CharZero K]
variable {A : Matrix (Fin (n+1)) (Fin (n+1)) K} {b τ h W k θ : Fin (n+1) → K}
variable {U : Submodule K (Fin (n+1) → K)}

/-- The absent origin is a root of the polynomial, not a synthetic feed
clock. The first two actual blocks pay the characteristic-zero 4+3 cut. -/
theorem clean_four_no_origin_impossible
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder p A b) (pay : 17 ≤ p)
    (G : UnitCleanFourFeed A b τ h W k θ U P)
    (inside : hiddenKernel b τ U ≤ zeroSpace A 8)
    (stable : (hiddenKernel b τ U).map (diag (nodes A)) ≤ hiddenKernel b τ U)
    (absent : (0 : K) ∉ weightedSites (nodes A) θ) : False := by
  let E : FeedChronology (nodes A) θ 4 := feedChronology G.sites
  have p0 : P.eval 0 = 0 := by
    rw [←origin_value ha G inside]
    by_contra live
    have c0 : nodes A 0 = 0 := by
      change mat A 1 0 = 0
      apply causal_mat ha
      intro j hj
      exact ((not_lt_of_ge (Fin.zero_le j)) hj).elim
    exact absent (mem_weightedSites.mpr ⟨0, live, c0⟩)
  have nonzero (i : Fin 4) : E.clock i ≠ 0 := by
    intro eq
    exact absent (eq ▸ E.site i)
  apply G.live
  refine rooted_four_three P (G.degree.trans (by decide)) p0 (nonzero 0) (nonzero 1)
    (E.clock_ne (by decide : (1 : Fin 4) ≠ 0)) ?_ ?_
  · intro R rd
    apply E.forward_primitive_zero ha ho pay G inside stable 0 R rd
    intro j hj
    exact ((not_lt_of_ge (Fin.zero_le j)) hj).elim
  · intro R rd
    have d : (R*(X-C (E.clock 0))).natDegree ≤ 3 :=
      natDegree_mul_le_of_le rd (natDegree_X_sub_C _).le
    apply E.forward_primitive_zero ha ho pay G inside stable 1 _ d
    intro j hj
    rw [before_one hj]
    simp only [eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero]

end NoOrigin

section Ordered
variable [LinearOrder K] [IsStrictOrderedRing K]

theorem FeedChronology.reverse_interval_zero (E : FeedChronology (nodes A) θ m)
    (B : UnitFourCompensated A b τ W U S Q)
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder p A b) (pay : 17 ≤ p)
    (G : UnitCleanFourFeed A b τ h W k θ U (ordinaryProfile Q))
    (inside : hiddenKernel b τ U ≤ zeroSpace A 8)
    (stable : (hiddenKernel b τ U).map (diag (nodes A)) ≤ hiddenKernel b τ U)
    (i : Fin m) (R : K[X]) (rd : R.natDegree ≤ 2)
    (masked : ∀ j, i < j → R.eval (E.clock j) = 0) :
    integral (E.clock i) 1 (R*ordinaryProfile Q) = 0 := by
  have paid := indicator_paid ho pay G inside stable (E.site i)
  have mass := B.block_mass_pos ho pay G (E.site i) paid
  refine B.reverse_mask_zero ha ho pay G inside stable (E.site i) mass.ne' R rd ?_
  intro z hz later
  obtain ⟨j, rfl⟩ := E.covers z hz
  exact masked j (E.ordered.lt_iff_lt.mp later)

/-- The exact six chronological windows. The sum over blocks has
already been collapsed by a strict first-row filter or its transpose. -/
theorem FeedChronology.opposed_moments_of_origin
    (E : FeedChronology (nodes A) θ 4) (zeroClock : E.clock 0 = 0)
    (B : UnitFourCompensated A b τ W U S Q)
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder p A b) (pay : 17 ≤ p)
    (G : UnitCleanFourFeed A b τ h W k θ U (ordinaryProfile Q))
    (inside : hiddenKernel b τ U ≤ zeroSpace A 8)
    (stable : (hiddenKernel b τ U).map (diag (nodes A)) ≤ hiddenKernel b τ U) :
    OpposedThreePivotMoments (ordinaryProfile Q) X 1 (E.clock 1) (E.clock 2) (E.clock 3) := by
  let P' := ordinaryProfile Q
  let a := E.clock 1
  let d := E.clock 2
  let c := E.clock 3
  have da : (X-C a : K[X]).natDegree ≤ 1 := (natDegree_X_sub_C _).le
  have dd : (X-C d : K[X]).natDegree ≤ 1 := (natDegree_X_sub_C _).le
  have dc : (X-C c : K[X]).natDegree ≤ 1 := (natDegree_X_sub_C _).le
  have xd : (X : K[X]).natDegree ≤ 1 := natDegree_X.le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    let R : K[X] := X*X^j.val
    have rd : R.natDegree ≤ 3 := natDegree_mul_le_of_le xd (monomial_degree_le (d:=2) j)
    have zero := E.forward_interval_zero ha ho pay G inside stable 1 R rd (by
      intro i hi
      rw [before_one hi]
      simp only [R, eval_mul, eval_X, zeroClock, zero_mul])
    have product : R*P' = X*P'*X^j.val := by dsimp only [R]; ac_rfl
    change integral 0 a (R*P') = 0 at zero
    rwa [product] at zero
  · intro j
    let R : K[X] := X*(X-C a)*X^j.val
    have rd : R.natDegree ≤ 3 := natDegree_mul_le_of_le
      (natDegree_mul_le_of_le xd da) (monomial_degree_le (d:=1) j)
    have zero := E.forward_interval_zero ha ho pay G inside stable 2 R rd (by
      intro i hi
      rcases before_two hi with eq | eq
      · rw [eq]
        simp only [R, eval_mul, eval_X, zeroClock, zero_mul]
      · rw [eq]
        simp only [R, a, eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero, zero_mul])
    have product : R*P' = X*(X-C a)*P'*X^j.val := by dsimp only [R]; ac_rfl
    change integral 0 d (R*P') = 0 at zero
    rwa [product] at zero
  · let R : K[X] := X*(X-C a)*(X-C d)
    have rd : R.natDegree ≤ 3 := natDegree_mul_le_of_le
      (natDegree_mul_le_of_le xd da) dd
    have zero := E.forward_interval_zero ha ho pay G inside stable 3 R rd (by
      intro i hi
      rcases before_three hi with eq | eq | eq
      · rw [eq]
        simp only [R, eval_mul, eval_X, zeroClock, zero_mul]
      · rw [eq]
        simp only [R, a, eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero, zero_mul]
      · rw [eq]
        simp only [R, d, eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero])
    exact zero
  · intro j
    have rd : ((X : K[X])^j.val).natDegree ≤ 2 := monomial_degree_le (d:=2) j
    have zero := E.reverse_interval_zero B ha ho pay G inside stable 3 (X^j.val) rd
      (fun _ hi => (no_after_three hi).elim)
    simpa only [one_mul, mul_comm] using zero
  · intro j
    let R : K[X] := (X-C c)*X^j.val
    have rd : R.natDegree ≤ 2 := natDegree_mul_le_of_le dc (monomial_degree_le (d:=1) j)
    have zero := E.reverse_interval_zero B ha ho pay G inside stable 2 R rd (by
      intro i hi
      rw [after_two hi]
      simp only [R, c, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul])
    have product : R*P' = (X-C c)*P'*X^j.val := by dsimp only [R]; ac_rfl
    change integral d 1 (R*P') = 0 at zero
    rw [product] at zero
    simpa only [one_mul] using zero
  · let R : K[X] := (X-C c)*(X-C d)
    have rd : R.natDegree ≤ 2 := natDegree_mul_le_of_le dc dd
    have zero := E.reverse_interval_zero B ha ho pay G inside stable 1 R rd (by
      intro i hi
      rcases after_one hi with eq | eq
      · rw [eq]
        simp only [R, d, eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero]
      · rw [eq]
        simp only [R, c, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul])
    simpa only [one_mul] using zero

section OriginDispatch
variable {A : Matrix (Fin (n+1)) (Fin (n+1)) K} {b τ h W k θ : Fin (n+1) → K}
variable {U : Submodule K (Fin (n+1) → K)}

/-- The three nonzero clocks are truly interior by whole-block hull
moments; their chronological order need not agree with their values. -/
theorem UnitFourCompensated.clean_four_origin_impossible
    (B : UnitFourCompensated A b τ W U S Q)
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder p A b) (pay : 17 ≤ p)
    (G : UnitCleanFourFeed A b τ h W k θ U (ordinaryProfile Q))
    (inside : hiddenKernel b τ U ≤ zeroSpace A 8)
    (stable : (hiddenKernel b τ U).map (diag (nodes A)) ≤ hiddenKernel b τ U)
    (origin : (0 : K) ∈ weightedSites (nodes A) θ) : False := by
  let E : FeedChronology (nodes A) θ 4 := feedChronology G.sites
  have zeroClock : E.clock 0 = 0 := E.clock_zero_of_origin (m:=3) ha G inside origin
  have pos (i : Fin 4) (ne : i ≠ 0) : E.clock i ∈ Set.Ioo (0 : K) 1 :=
    B.nonzero_clock_interior ho pay G origin (E.site i)
      (fun ez => ne (E.clock_injective (ez.trans zeroClock.symm)))
  have paid := E.opposed_moments_of_origin zeroClock B ha ho pay G inside stable
  have d := G.degree
  have up : (X : K[X]).natDegree + (ordinaryProfile Q).natDegree + 2 ≤ 19 := by
    rw [natDegree_X]
    omega
  have vp : (1 : K[X]).natDegree + (ordinaryProfile Q).natDegree + 2 ≤ 19 := by
    rw [natDegree_one]
    omega
  have high := paid.six_le_natDegree G.live
    (pos 1 (by decide)) (pos 2 (by decide)) (pos 3 (by decide))
    (E.clock_ne (by decide : (1 : Fin 4) ≠ 2))
    (E.clock_ne (by decide : (1 : Fin 4) ≠ 3))
    (E.clock_ne (by decide : (2 : Fin 4) ≠ 3))
    (fun x hx => by simpa only [eval_X] using hx.1)
    (fun x _ => by simpa only [eval_one] using (zero_lt_one : (0 : K) < 1)) up vp
  omega

/-- Shared clean-four endgame, with no rank-specific or stage-bound
claim. The geometric producer supplies the exact support and weights. -/
theorem UnitFourCompensated.clean_four_impossible
    (B : UnitFourCompensated A b τ W U S Q)
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder p A b) (pay : 17 ≤ p)
    (G : UnitCleanFourFeed A b τ h W k θ U (ordinaryProfile Q))
    (inside : hiddenKernel b τ U ≤ zeroSpace A 8)
    (stable : (hiddenKernel b τ U).map (diag (nodes A)) ≤ hiddenKernel b τ U) : False := by
  classical
  by_cases origin : (0 : K) ∈ weightedSites (nodes A) θ
  · exact B.clean_four_origin_impossible ha ho pay G inside stable origin
  · exact clean_four_no_origin_impossible ha ho pay G inside stable origin

end OriginDispatch
end Ordered

end
end RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour
