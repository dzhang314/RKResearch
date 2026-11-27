import RKCert.ReviewedNative.GroupedTerminalRefund
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Abel

namespace RKResearch.Certified.ProtectedTerminalRefund

open GroupedTerminalRefund

section LowPacket

variable {K V High Low Out : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup High] [Module K High] [AddCommGroup Low] [Module K Low]
    [AddCommGroup Out] [Module K Out]

/-- At equality in the paid block count, a protected eigenvector killed
    by the high readout already belongs to the lower physical block. -/
theorem protected_mem_low (P : V →ₗ[K] V) (hP : Function.Injective P)
    (hi : High →ₗ[K] V) (lo : Low →ₗ[K] V) (D : V →ₗ[K] Out)
    (hs : Function.Surjective (hi.coprod (P.comp lo)))
    (hhi : Function.Injective (D.comp hi)) (hz : D.comp (P.comp lo) = 0)
    (e : V) (c : K) (hc : c ≠ 0) (he : P e = c • e) (hde : D e = 0) :
    e ∈ lo.range := by
  obtain ⟨⟨x,y⟩,hxy⟩ := hs e
  change hi x + P (lo y) = e at hxy
  have hy : D (P (lo y)) = 0 := LinearMap.congr_fun hz y
  have hx : D (hi x) = 0 := by
    simpa only [map_add, hy, add_zero, hde] using congrArg D hxy
  have hx0 : x = 0 := (D.comp hi).map_eq_zero_iff hhi |>.mp hx
  rw [hx0, map_zero, zero_add] at hxy
  have ht : lo y = c⁻¹ • e := hP <| by
    rw [hxy, map_smul, he, smul_smul, inv_mul_cancel₀ hc, one_smul]
  refine ⟨c • y,?_⟩
  rw [map_smul, ht, smul_smul, mul_inv_cancel₀ hc, one_smul]

end LowPacket

section ClockWitness

variable {K V W H : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [AddCommGroup H] [Module K H]

/-- Weighted discrepancies supported on live representatives are zero
    when the clock frame separates those representatives. -/
theorem vanish_supported_discrepancy (F : H →ₗ[K] V) (R : V →ₗ[K] W)
    (hs : Function.Surjective (R.comp F)) (l : Module.Dual K W)
    (h : F.dualMap (R.dualMap l) = 0) : l = 0 := by
  apply LinearMap.ext
  intro w
  obtain ⟨t,ht⟩ := hs w
  rw [← ht]
  exact LinearMap.congr_fun h t

/-- The actual two top sources add to a physical site commutator.
    The subtraction in the first source uses (J((X-a)P)=(X-a)JP-J^2P). -/
theorem discrepancy_sum (S Y : V →ₗ[K] V) (a : K) (u m j2 : V)
    (hm : Y m = a • m) :
    (S (Y u - a • u) - (Y (m + S u) - a • (m + S u) - j2)) +
      (S (S u - u) - (j2 - (m + S u))) =
    (S (S u) + S (Y u) - Y (S u)) + m := by
  simp only [map_sub, map_smul, map_add, smul_add, hm]
  abel

end ClockWitness

section ExactRank

variable {K V High Low Out : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup High] [Module K High] [AddCommGroup Low] [Module K Low]
    [AddCommGroup Out] [Module K Out]
    [FiniteDimensional K V] [FiniteDimensional K High] [FiniteDimensional K Low]

/-- Thus the exact stage count, not an assumed onto map, supplies
    the required physical representation. -/
theorem protected_mem_low_at_exact_count (P : V →ₗ[K] V) (hP : Function.Injective P)
    (hi : High →ₗ[K] V) (lo : Low →ₗ[K] V) (D : V →ₗ[K] Out)
    (hs : Module.finrank K (High × Low) = Module.finrank K V)
    (hlo : Function.Injective lo) (hhi : Function.Injective (D.comp hi))
    (hz : D.comp (P.comp lo) = 0)
    (e : V) (c : K) (hc : c ≠ 0) (he : P e = c • e) (hde : D e = 0) :
    e ∈ lo.range :=
  protected_mem_low P hP hi lo D
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank hs).mp
      (packet_step hP hlo hhi hz)) hhi hz e c hc he hde

end ExactRank

/-- Arbitrary data on the active sites alone can be interpolated
    by the clock frame avoiding the single protected port. -/
theorem clockFrame_surjective_square {K : Type*} [Field K] {n : ℕ}
    (hn : 0 < n) (x : Fin n → K) (v : K) (hx : Function.Injective x)
    (hv : ∀ i, x i ≠ v) : Function.Surjective (clockFrame (d := n) x v) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
    (clockFrame_injective hn le_rfl x v hx hv)

theorem exact_overlap_counts (r n t old d lo : ℕ)
    (ht : t ≤ n) (hn : r + 2 ≤ n) (hlow : lo ≤ old)
    (hrefund : t - 1 ≤ d + (n - (r+2))) (hpacket : lo + d ≤ old)
    (hbudget : old + (n - t) ≤ lo + r + 1) :
    old = lo + d ∧ old + (n - t) = lo + r + 1 ∧ n - t ≤ r + 1 := by
  omega

section Triangular

variable {K : Type*} [Field K]

/-- Recover the active representatives in literal chronological order. -/
theorem kill_lower_unit {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K)
    (hdiag : ∀ i, A i i = 1) (htri : ∀ i j, i < j → A i j = 0)
    (h : A.mulVec u = 0) : u = 0 := by
  have hzero (k : ℕ) : ∀ i : Fin n, i.val = k → u i = 0 := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro i hi
      have he : (∑ j, A i j * u j) = 0 := congrFun h i
      rw [Finset.sum_eq_single i] at he
      · simpa only [hdiag, one_mul] using he
      · intro j _ hji
        rcases lt_or_gt_of_ne hji with hh | hh
        · have hj : j.val < k := by
            have : j.val < i.val := hh
            omega
          rw [ih j.val hj j rfl, mul_zero]
        · rw [htri i j hh, zero_mul]
      · simp
  funext i
  exact hzero i.val i rfl

/-- The chronological restriction of the site discrepancy commutator
    has diagonal one, including at repeated/outside clock values. -/
theorem kill_site_commutator {n : ℕ} (S : Matrix (Fin n) (Fin n) K)
    (y u : Fin n → K) (hdiag : ∀ i, S i i = 1)
    (htri : ∀ i j, i < j → S i j = 0)
    (h : (S*S + S*Matrix.diagonal y - Matrix.diagonal y*S).mulVec u = 0) :
    u = 0 := by
  apply kill_lower_unit _ u _ _ h
  · intro i
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
      hdiag, one_mul, mul_one, add_sub_cancel_right]
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [hdiag]
    · intro j _ hji
      rcases lt_or_gt_of_ne hji with hh | hh
      · rw [htri j i hh, mul_zero]
      · rw [htri i j hh, zero_mul]
    · simp
  · intro i j hij
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
      htri i j hij, zero_mul, mul_zero, add_zero, sub_zero]
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rcases lt_or_ge i k with hh | hh
    · rw [htri i k hh, zero_mul]
    · rw [htri k j (lt_of_le_of_lt hh hij), mul_zero]

end Triangular

end RKResearch.Certified.ProtectedTerminalRefund
