module

public import RKCert.ReviewedNative.LocalLinearUnitFourFeed

@[expose] public section

/-! # Paid four-clock indicators and forward block coefficients

An indicator is 1 on every original feed row of its clock, including
repeated clocks, and 0 elsewhere. Clock block chronology is read at the
first physical occurrence. No new tableau or order assertion is made. -/
namespace RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour

open RKResearch Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b τ h W k θ : Fin s → K}
variable {U : Submodule K (Fin s → K)} {P : K[X]}

def feedRows (c θ : Fin s → K) (x : K) : Finset (Fin s) :=
  Finset.univ.filter fun i => θ i ≠ 0 ∧ c i = x

def indicator (c θ : Fin s → K) (x : K) : Fin s → K :=
  fun i => if θ i ≠ 0 ∧ c i = x then 1 else 0

def blockMass (c θ v : Fin s → K) (x : K) : K :=
  row v (indicator c θ x)

theorem feedRows_nonempty {c θ : Fin s → K} {x : K}
    (hx : x ∈ weightedSites c θ) : (feedRows c θ x).Nonempty := by
  obtain ⟨i, hi, eq⟩ := mem_weightedSites.mp hx
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi, eq⟩⟩

def firstRow (c θ : Fin s → K) (x : K) (hx : x ∈ weightedSites c θ) : Fin s :=
  (feedRows c θ x).min' (feedRows_nonempty hx)

theorem firstRow_spec (c θ : Fin s → K) (x : K) (hx : x ∈ weightedSites c θ) :
    θ (firstRow c θ x hx) ≠ 0 ∧ c (firstRow c θ x hx) = x :=
  (Finset.mem_filter.mp (Finset.min'_mem (feedRows c θ x) (feedRows_nonempty hx))).2

theorem firstRow_le (c θ : Fin s → K) (x : K) (hx : x ∈ weightedSites c θ)
    {i : Fin s} (hi : θ i ≠ 0) (eq : c i = x) : firstRow c θ x hx ≤ i :=
  Finset.min'_le (feedRows c θ x) i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi, eq⟩)

theorem firstRow_eq_implies_clock_eq {c θ : Fin s → K} {x z : K}
    (hx : x ∈ weightedSites c θ) (hz : z ∈ weightedSites c θ)
    (same : firstRow c θ x hx = firstRow c θ z hz) : x = z := by
  calc
    x = c (firstRow c θ x hx) := (firstRow_spec c θ x hx).2.symm
    _ = c (firstRow c θ z hz) := congrArg c same
    _ = z := (firstRow_spec c θ z hz).2

def cardinalTest (c θ : Fin s → K) (P : K[X]) (x : K) : K[X] :=
  Polynomial.C (P.eval x)⁻¹ * Lagrange.basis (weightedSites c θ) id x

/-- Coefficient from source block x to target block z. -/
def coefficient (A : Matrix (Fin s) (Fin s) K) (θ : Fin s → K)
    (P : K[X]) (z x : K) : K :=
  (primitive (cardinalTest (nodes A) θ P x * P)).eval z

theorem nonzero_profile_at_site (G : UnitCleanFourFeed A b τ h W k θ U P)
    {x : K} (hx : x ∈ weightedSites (nodes A) θ) : P.eval x ≠ 0 := by
  obtain ⟨i, hi, eq⟩ := mem_weightedSites.mp hx
  rw [←eq, ←G.value i hi]
  exact hi

theorem cardinalTest_degree (G : UnitCleanFourFeed A b τ h W k θ U P)
    {x : K} (hx : x ∈ weightedSites (nodes A) θ) :
    (cardinalTest (nodes A) θ P x).natDegree ≤ 3 := by
  have d := Lagrange.natDegree_basis (Set.injOn_id _) hx
  unfold cardinalTest
  apply natDegree_mul_le.trans
  rw [natDegree_C, d, G.sites] <;> decide

/-- Exact full-row indicator, not an indicator of a chosen representative. -/
theorem cardinalTest_evaluation (G : UnitCleanFourFeed A b τ h W k θ U P)
    {x : K} (hx : x ∈ weightedSites (nodes A) θ) :
    weightedEval (nodes A) θ (cardinalTest (nodes A) θ P x) =
      indicator (nodes A) θ x := by
  let c := nodes A
  let D := weightedSites c θ
  have pd := nonzero_profile_at_site G hx
  ext i
  by_cases hi : θ i = 0
  · simp [weightedEval_apply, indicator, hi]
  have atD : c i ∈ D := mem_weightedSites.mpr ⟨i, hi, rfl⟩
  by_cases eq : c i = x
  · have ev : (Lagrange.basis D id x).eval x = 1 :=
      Lagrange.eval_basis_self (Set.injOn_id _) hx
    have pi : θ i = P.eval x := (G.value i hi).trans (congrArg P.eval eq)
    change weightedEval c θ (cardinalTest c θ P x) i = indicator c θ x i
    rw [weightedEval_apply, cardinalTest, eval_mul, eval_C, eq, ev, mul_one, pi, inv_mul_cancel₀ pd]
    exact (if_pos ⟨hi, eq⟩).symm
  · have ev : (Lagrange.basis D id x).eval (c i) = 0 :=
      Lagrange.eval_basis_of_ne (v:=id) (Ne.symm eq) atD
    change weightedEval c θ (cardinalTest c θ P x) i = indicator c θ x i
    rw [weightedEval_apply, cardinalTest, eval_mul, eval_C, ev, mul_zero, zero_mul]
    exact (if_neg (fun h => eq h.2)).symm

/-- Expand the entire feed in the literal indicators, with its original
signed coefficients. -/
theorem weightedEval_eq_indicator_sum (G : UnitCleanFourFeed A b τ h W k θ U P)
    (R : K[X]) :
    weightedEval (nodes A) θ R = ∑ x ∈ weightedSites (nodes A) θ,
      (R.eval x * P.eval x) • indicator (nodes A) θ x := by
  let c := nodes A
  change weightedEval c θ R = _
  ext i
  rw [weightedEval_apply, Finset.sum_apply]
  by_cases hi : θ i = 0
  · rw [hi, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro x _
    simp [Pi.smul_apply, indicator, hi]
  have atD : c i ∈ weightedSites c θ := mem_weightedSites.mpr ⟨i, hi, rfl⟩
  rw [Finset.sum_eq_single_of_mem (c i) atD]
  · rw [Pi.smul_apply, smul_eq_mul, indicator, if_pos ⟨hi,rfl⟩, mul_one]
    rw [G.value i hi]
  · intro x _ off
    rw [Pi.smul_apply, indicator, if_neg (fun h => off h.2.symm), smul_zero]

/-- A clock carrying weight only on fed rows can use the checked signed
grouping by clock; the ambient all-stage clock image then restricts to the
actual feed sites. -/
theorem sum_by_feed_clock (c θ v : Fin s → K)
    (sub : ∀ i, v i ≠ 0 → θ i ≠ 0) (T : K → K) :
    (∑ i, v i * T (c i)) =
      ∑ x ∈ weightedSites c θ, blockMass c θ v x * T x := by
  have mass (x : K) : blockMass c θ v x = clockMass c v x := by
    simp only [blockMass, row_apply, dotProduct, clockMass, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases z : v i = 0
    · simp [z]
    · by_cases eq : c i = x <;> simp [indicator, sub i z, eq]
  have active : weightedSites c v ⊆ weightedSites c θ := by
    intro x hx
    obtain ⟨i, hi, eq⟩ := mem_weightedSites.mp hx
    exact mem_weightedSites.mpr ⟨i, sub i hi, eq⟩
  have all : weightedSites c θ ⊆ Finset.univ.image c := by
    intro x hx
    obtain ⟨i, _, eq⟩ := mem_weightedSites.mp hx
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, eq⟩
  calc
    _ = ∑ x ∈ Finset.univ.image c, clockMass c v x * T x := weighted_sum_by_clock c v T
    _ = ∑ x ∈ weightedSites c θ, clockMass c v x * T x := by
      symm
      apply Finset.sum_subset all
      intro x _ off
      rw [clockMass_zero_of_not_site (fun hx => off (active hx)), zero_mul]
    _ = _ := by simp only [mass]

section PaidForward
variable [CharZero K]

/-- The geometric feed pays the whole rectangular degree-three family
in E8 and its exact forward primitive defect in F9. -/
theorem forward_paid (ho : HasOrder p A b) (pay : 17 ≤ p)
    (G : UnitCleanFourFeed A b τ h W k θ U P)
    (inside : hiddenKernel b τ U ≤ zeroSpace A 8)
    (stable : (hiddenKernel b τ U).map (diag (nodes A)) ≤ hiddenKernel b τ U)
    (R : K[X]) (rd : R.natDegree ≤ 3) :
    weightedEval (nodes A) θ R ∈ treeSpace A 8 ∧
      mat A (weightedEval (nodes A) θ R) - evalNodes A (primitive (R*P)) ∈ zeroSpace A 9 := by
  have deg : (R*P).natDegree ≤ 8 := natDegree_mul_le_of_le rd G.degree
  have h8 : h * evalNodes A R ∈ zeroSpace A 8 :=
    zeroSpace_mul_treeSpace ho (m:=5) (n:=3) (by omega) G.headGrade
      (evalNodes_mem_treeSpace A R rd)
  have k8 : weightedEval (nodes A) k R ∈ zeroSpace A 8 :=
    inside (reflected_clock_weighted_core stable G.correction R)
  have eq : weightedEval (nodes A) θ R =
      evalNodes A (R*P) - h*evalNodes A R - weightedEval (nodes A) k R := by
    rw [G.formula]
    ext i
    simp only [weightedEval_apply, evalNodes_apply, Pi.sub_apply, Pi.mul_apply, eval_mul]
    ring
  refine ⟨?_, ?_⟩
  · rw [eq]
    exact (treeSpace A 8).sub_mem ((treeSpace A 8).sub_mem
      (evalNodes_mem_treeSpace A _ deg) (zeroSpace_le_treeSpace A 8 h8))
      (zeroSpace_le_treeSpace A 8 k8)
  · rw [eq, map_sub, map_sub]
    have pr := primitive_defect A (R*P) (q:=8) deg
    convert (zeroSpace A 9).sub_mem ((zeroSpace A 9).sub_mem pr
      (mat_zeroSpace_charZero A 8 h8)) (mat_zeroSpace_charZero A 8 k8) using 1
    abel

theorem forward_eval (ho : HasOrder p A b) (pay : 17 ≤ p)
    (G : UnitCleanFourFeed A b τ h W k θ U P)
    (inside : hiddenKernel b τ U ≤ zeroSpace A 8)
    (stable : (hiddenKernel b τ U).map (diag (nodes A)) ≤ hiddenKernel b τ U)
    (R : K[X]) (rd : R.natDegree ≤ 3) {i : Fin s} (hi : θ i ≠ 0) :
    mat A (weightedEval (nodes A) θ R) i = (primitive (R*P)).eval (nodes A i) := by
  have eq := G.clean i hi _ (forward_paid ho pay G inside stable R rd).2
  exact sub_eq_zero.mp (by simpa only [Pi.sub_apply, evalNodes_apply] using eq)

theorem indicator_paid (ho : HasOrder p A b) (pay : 17 ≤ p)
    (G : UnitCleanFourFeed A b τ h W k θ U P)
    (inside : hiddenKernel b τ U ≤ zeroSpace A 8)
    (stable : (hiddenKernel b τ U).map (diag (nodes A)) ≤ hiddenKernel b τ U)
    {x : K} (hx : x ∈ weightedSites (nodes A) θ) :
    indicator (nodes A) θ x ∈ treeSpace A 8 := by
  rw [←cardinalTest_evaluation G hx]
  exact (forward_paid ho pay G inside stable _ (cardinalTest_degree G hx)).1

theorem coefficient_eval (ho : HasOrder p A b) (pay : 17 ≤ p)
    (G : UnitCleanFourFeed A b τ h W k θ U P)
    (inside : hiddenKernel b τ U ≤ zeroSpace A 8)
    (stable : (hiddenKernel b τ U).map (diag (nodes A)) ≤ hiddenKernel b τ U)
    {x : K} (hx : x ∈ weightedSites (nodes A) θ) {i : Fin s} (hi : θ i ≠ 0) :
    mat A (indicator (nodes A) θ x) i = coefficient A θ P (nodes A i) x := by
  rw [←cardinalTest_evaluation G hx]
  exact forward_eval ho pay G inside stable _ (cardinalTest_degree G hx) hi

theorem coefficient_eq_zero_before (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder p A b) (pay : 17 ≤ p)
    (G : UnitCleanFourFeed A b τ h W k θ U P)
    (inside : hiddenKernel b τ U ≤ zeroSpace A 8)
    (stable : (hiddenKernel b τ U).map (diag (nodes A)) ≤ hiddenKernel b τ U)
    {z x : K} (hz : z ∈ weightedSites (nodes A) θ) (hx : x ∈ weightedSites (nodes A) θ)
    (le : firstRow (nodes A) θ z hz ≤ firstRow (nodes A) θ x hx) :
    coefficient A θ P z x = 0 := by
  let c := nodes A
  let i := firstRow c θ z hz
  obtain ⟨hi, iz⟩ := firstRow_spec c θ z hz
  have zero : mat A (indicator c θ x) i = 0 := by
    apply causal_mat ha
    intro j before
    have before' : j < i := before
    have none : ¬(θ j ≠ 0 ∧ c j = x) := by
      rintro ⟨live, clock⟩
      exact (not_lt_of_ge (le.trans (firstRow_le c θ x hx live clock))) before'
    simp [indicator, none]
  have eq := coefficient_eval ho pay G inside stable hx hi
  change mat A (indicator c θ x) i = coefficient A θ P (c i) x at eq
  rw [iz] at eq
  exact eq.symm.trans zero

/-- The rows of the physical block coefficients carry the full paid
forward polynomial tests. -/
theorem forward_block_moment (ho : HasOrder p A b) (pay : 17 ≤ p)
    (G : UnitCleanFourFeed A b τ h W k θ U P)
    (inside : hiddenKernel b τ U ≤ zeroSpace A 8)
    (stable : (hiddenKernel b τ U).map (diag (nodes A)) ≤ hiddenKernel b τ U)
    {z : K} (hz : z ∈ weightedSites (nodes A) θ) (R : K[X]) (rd : R.natDegree ≤ 3) :
    (∑ x ∈ weightedSites (nodes A) θ,
      (R.eval x * P.eval x) * coefficient A θ P z x) = (primitive (R*P)).eval z := by
  obtain ⟨i, hi, iz⟩ := mem_weightedSites.mp hz
  have eq := forward_eval ho pay G inside stable R rd hi
  rw [weightedEval_eq_indicator_sum G R, map_sum, Finset.sum_apply, iz] at eq
  simp only [map_smul, Pi.smul_apply, smul_eq_mul] at eq
  calc
    _ = ∑ x ∈ weightedSites (nodes A) θ,
          (R.eval x * P.eval x) * mat A (indicator (nodes A) θ x) i := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [coefficient_eval ho pay G inside stable hx hi, iz]
    _ = _ := eq

/-- A paid multiplier vanishing on all earlier blocks needs no
pointwise injectivity or assumptions on later physical rows. -/
theorem forward_mask_zero (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder p A b) (pay : 17 ≤ p)
    (G : UnitCleanFourFeed A b τ h W k θ U P)
    (inside : hiddenKernel b τ U ≤ zeroSpace A 8)
    (stable : (hiddenKernel b τ U).map (diag (nodes A)) ≤ hiddenKernel b τ U)
    {z : K} (hz : z ∈ weightedSites (nodes A) θ) (R : K[X]) (rd : R.natDegree ≤ 3)
    (filter : ∀ x, ∀ hx : x ∈ weightedSites (nodes A) θ,
      firstRow (nodes A) θ x hx < firstRow (nodes A) θ z hz → R.eval x = 0) :
    (primitive (R*P)).eval z = 0 := by
  rw [←forward_block_moment ho pay G inside stable hz R rd]
  apply Finset.sum_eq_zero
  intro x hx
  by_cases before : firstRow (nodes A) θ x hx < firstRow (nodes A) θ z hz
  · rw [filter x hx before, zero_mul, zero_mul]
  · rw [coefficient_eq_zero_before ha ho pay G inside stable hz hx (le_of_not_gt before), mul_zero]

end PaidForward

theorem origin_value {n : ℕ} {A : Matrix (Fin (n+1)) (Fin (n+1)) K}
    {b τ h W k θ : Fin (n+1) → K} {U : Submodule K (Fin (n+1) → K)}
    (ha : ∀ i j, i ≤ j → A i j = 0) (G : UnitCleanFourFeed A b τ h W k θ U P)
    (inside : hiddenKernel b τ U ≤ zeroSpace A 8) : θ 0 = P.eval 0 := by
  have c0 : nodes A 0 = 0 := by
    change mat A 1 0 = 0
    apply causal_mat ha
    intro j hj
    have hn : j.val < 0 := hj
    omega
  have h0 := origin_zeroSpace ha 5 G.headGrade
  have k0 := origin_zeroSpace ha 8 (inside G.correction)
  change h 0 = 0 at h0
  change k 0 = 0 at k0
  rw [G.formula]
  simp only [Pi.sub_apply, evalNodes_apply, c0, h0, k0, sub_zero]

theorem firstRow_origin {n : ℕ} {A : Matrix (Fin (n+1)) (Fin (n+1)) K}
    {b τ h W k θ : Fin (n+1) → K} {U : Submodule K (Fin (n+1) → K)}
    (ha : ∀ i j, i ≤ j → A i j = 0) (G : UnitCleanFourFeed A b τ h W k θ U P)
    (inside : hiddenKernel b τ U ≤ zeroSpace A 8)
    (origin : (0 : K) ∈ weightedSites (nodes A) θ) :
    firstRow (nodes A) θ 0 origin = 0 := by
  have nP := nonzero_profile_at_site G origin
  have live : θ 0 ≠ 0 := (origin_value ha G inside).symm ▸ nP
  have c0 : nodes A 0 = 0 := by
    change mat A 1 0 = 0
    apply causal_mat ha
    intro j hj
    have hn : j.val < 0 := hj
    omega
  exact le_antisymm (firstRow_le (nodes A) θ 0 origin live c0) (Fin.zero_le _)

end
end RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour
