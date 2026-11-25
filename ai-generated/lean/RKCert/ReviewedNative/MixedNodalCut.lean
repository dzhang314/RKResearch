module

public import RKCert.ReviewedNative.NodalMaskNullity
public import RKCert.ReviewedNative.NonsingularNodalCut

@[expose] public section

/-! # Actual mixed-diagonal primal and dual cut budgets

These adapters reuse the published native clock bands and defect tests.
There is no nonsingularity requirement on the whole tableau. The kernel
receipt is for the invariant counted side alone.
-/

namespace RKResearch.Certified.Graded

open Module Polynomial FiniteRootedTree
open scoped BigOperators Matrix Polynomial

noncomputable section

variable {K : Type*} [Field K] {s p z : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

private theorem nodalColumn_eq_coeffEval (A : Matrix (Fin s) (Fin s) K)
    (q : ℕ) (Q : degreeLT K (q+1)) :
    nodalColumn A (Q : K[X]) = coeffEval A q (degreeLTEquiv K (q+1) Q) := by
  ext i
  rw [nodalColumn_apply,Polynomial.eval_eq_sum_degreeLTEquiv Q.property,coeffEval_apply]
  simp only [normTree_clockTree,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

private theorem nodalRow_eq_covClock (A : Matrix (Fin s) (Fin s) K)
    (b : Fin s → K) (q : ℕ) (Q : degreeLT K (q+1)) :
    nodalRow A b (Q : K[X]) = covClock A b q (degreeLTEquiv K (q+1) Q) := by
  let F : (Fin s → K) →ₗ[K] ClockCovector K s := (dotProductBilin K K).comp (diag b)
  change F (nodalColumn A (Q : K[X])) = _
  rw [nodalColumn_eq_coeffEval A q Q,coeffEval_apply,map_sum]
  change (∑ i : Fin (q+1), F (degreeLTEquiv K (q+1) Q i • normTree A (clockTree i.val))) =
    ∑ i : Fin (q+1), degreeLTEquiv K (q+1) Q i • probe A b i.val
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,normTree_clockTree] <;> rfl

private theorem polyClockBand_inj_of_coeff {V : Type*} [AddCommGroup V] [Module K V]
    (L : K[X] →ₗ[K] V) (q : ℕ) (f : (Fin (q+1) → K) →ₗ[K] V)
    (h : ∀ Q : degreeLT K (q+1), L (Q : K[X]) = f (degreeLTEquiv K (q+1) Q))
    (hf : Function.Injective f) :
    Function.Injective (L.comp (degreeLT K (q+1)).subtype) := by
  intro Q S he
  apply (degreeLTEquiv K (q+1)).injective
  apply hf
  exact (h Q).symm.trans (he.trans (h S))

private theorem coeffEval_inj_paid (ho : RKResearch.HasOrder p A b) (q : ℕ) (pay : 2*q+1 ≤ p) :
    Function.Injective (coeffEval A q) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a h
  exact paid_coeffEval_eq_zero ho pay a (fun k => by rw [h,map_zero])

private theorem nodalCovClock_pair (q : ℕ) (a : Fin (q+1) → K) (k : ℕ) :
    covClock A b q a (normTree A (clockTree k)) = probe A b k (coeffEval A q a) := by
  rw [coeffEval_apply,map_sum]
  change (∑ i : Fin (q+1), a i • probe A b i.val) (normTree A (clockTree k)) = _
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  have h : probe A b j.val (normTree A (clockTree k)) =
      probe A b k (normTree A (clockTree j.val)) := by
    simp only [probe,row_apply,dotProduct,normTree_clockTree]
    apply Finset.sum_congr rfl
    intro i _
    ac_rfl
  rw [LinearMap.smul_apply,map_smul,h]

private theorem covClock_inj_paid (ho : RKResearch.HasOrder p A b) (q : ℕ) (pay : 2*q+1 ≤ p) :
    Function.Injective (covClock A b q) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a h
  apply paid_coeffEval_eq_zero ho pay a
  intro k
  simp only [← nodalCovClock_pair q a k.val,h,LinearMap.zero_apply]

/-- Paid primal polynomial steps in the genuine reviewed tree spaces. -/
theorem nodalColumn_paidGeometry (ho : RKResearch.HasOrder p A b) :
    PaidMaskGeometry (nodalColumn A) (volterra A) (treeSpace A) p where
  band_injective q hp :=
    polyClockBand_inj_of_coeff _ _ _ (nodalColumn_eq_coeffEval A q) (coeffEval_inj_paid ho q hp)
  band_le j q hq _ := by
    rw [polyClockBand_nodalColumn]
    rintro _ ⟨a,rfl⟩
    exact treeSpace_mono A hq (coeffEval_mem_treeSpace A q a)
  step_le j hp := by
    rintro _ ⟨v,hv,rfl⟩
    exact zeroSpace_le_treeSpace A (j+2) (volterra_treeSpace ho j (by omega) hv)
  separated j q hq hp := by
    rw [polyClockBand_nodalColumn]
    apply le_antisymm _ bot_le
    intro v hv
    obtain ⟨⟨a,ha⟩,⟨u,hu,e⟩⟩ := Submodule.mem_inf.mp hv
    have h : a = 0 := by
      apply paid_coeffEval_eq_zero ho (by omega)
      intro k
      have hk := k.isLt
      rw [ha,← e]
      exact probe_zeroSpace ho (by omega) (volterra_treeSpace ho j (by omega) hu)
    rw [← ha,h,map_zero]
    exact (⊥ : Submodule K (Fin s → K)).zero_mem

private theorem topCovClock_le (r : ℕ) :
    (covClock A b (min r (p-1-r))).range ≤ dualCensusSpace A b p r := by
  cases r with
  | zero =>
    rw [show min 0 (p-1-0) = 0 from Nat.zero_min _]
    exact le_rfl
  | succ r =>
    cases r with
    | zero =>
      change (covClock A b (min 1 (p-1-1))).range ≤ dualCensusSpace A b p 1
      rw [show p-1-1 = p-2 by omega]
      exact le_rfl
    | succ r => exact le_sup_left

/-- The existing native weighted-output census supplies the same
interface on the honest dual.  No weighted-transpose conjugation is used. -/
theorem nodalRow_paidGeometry (ho : RKResearch.HasOrder p A b) :
    PaidMaskGeometry (nodalRow A b) (volterra A).dualMap (dualCensusSpace A b p) p where
  band_injective q hp :=
    polyClockBand_inj_of_coeff _ _ _ (nodalRow_eq_covClock A b q) (covClock_inj_paid ho q hp)
  band_le j q hq hp := by
    have hh : q ≤ min j (p-1-j) := le_min hq (by omega)
    refine (polyClockBand_mono (nodalRow A b) hh).trans ?_
    rw [polyClockBand_nodalRow]
    exact topCovClock_le j
  step_le j _ := by
    change (dualCensusSpace A b p j).map (volterra A).dualMap ≤
      (covClock A b (min (j+2) (p-1-(j+2)))).range ⊔
      (dualCensusSpace A b p j).map (volterra A).dualMap
    exact le_sup_right
  separated j q hq hp := by
    rw [polyClockBand_nodalRow]
    apply le_antisymm _ bot_le
    intro f hf
    obtain ⟨⟨a,ha⟩,⟨g,hg,hgf⟩⟩ := Submodule.mem_inf.mp hf
    have hzero : a = 0 := by
      apply paid_coeffEval_eq_zero ho (by omega)
      intro k
      have hpow : normTree A (clockTree k.val) ∈ treeSpace A q := by
        rw [← coeffEval_single A q k]
        exact coeffEval_mem_treeSpace A q _
      have hz : volterra A (normTree A (clockTree k.val)) ∈ zeroSpace A (q+2) :=
        volterra_treeSpace ho q (by omega) hpow
      rw [← nodalCovClock_pair q a k.val,ha,← hgf]
      exact dualCensusSpace_silent ho j (q+2) (by omega) g hg _ hz
    rw [← ha,hzero,map_zero]
    exact (⊥ : Submodule K (ClockCovector K s)).zero_mem

/-- The actual primal masked columns on an invariant subspace. -/
theorem nodalColumn_localNullity_cut (ho : RKResearch.HasOrder p A b)
    (P : K[X]) (hP : P ≠ 0) (hpos : 2*P.natDegree < p)
    (W : Submodule K (Fin s → K)) (hW : W.map (volterra A) ≤ W)
    (hseed : ∀ Q : K[X], nodalColumn A (P*Q) ∈ W)
    (hz : finrank K (W ⊓ (volterra A).ker : Submodule K (Fin s → K)) ≤ z) :
    localNullityCutFloor (p-2*P.natDegree) z ≤ finrank K W :=
  maskedParityPacket_localNullity_cut_floor (nodalColumn_paidGeometry ho)
    P hP (m := p-2*P.natDegree) (z := z) (by omega) (by omega) W hW hseed hz

/-- The actual measured covectors on the annihilator of an invariant
opposite side. This does not invert the weight diagonal. -/
theorem nodalRow_localNullity_cut (ho : RKResearch.HasOrder p A b)
    (P : K[X]) (hP : P ≠ 0) (hpos : 2*P.natDegree < p)
    (W : Submodule K (Fin s → K)) (hW : W.map (volterra A) ≤ W)
    (hseed : ∀ Q : K[X], nodalRow A b (P*Q) ∈ W.dualAnnihilator)
    (hz : finrank K
      (W.dualAnnihilator ⊓ (volterra A).dualMap.ker : Submodule K (ClockCovector K s)) ≤ z) :
    localNullityCutFloor (p-2*P.natDegree) z ≤ finrank K W.dualAnnihilator := by
  apply maskedParityPacket_localNullity_cut_floor (nodalRow_paidGeometry ho) P hP
    (m := p-2*P.natDegree) (z := z) (by omega) (by omega) W.dualAnnihilator _ hseed hz
  rintro _ ⟨f,hf,rfl⟩
  apply (Submodule.mem_dualAnnihilator _).mpr
  intro v hv
  exact (Submodule.mem_dualAnnihilator _).mp hf _ (hW ⟨v,hv,rfl⟩)

/-- Primal local-kernel cutoff of a rooted physical prefix. Zeros in
the discarded prefix do not enter hz. -/
theorem mixed_head_clock_cut_of_kernel (ho : RKResearch.HasOrder p A b)
    (ha : A.IsLowerTriangular) (S : Finset (Fin s)) (hS : ∀ i ∈ S, ∀ j ≤ i, j ∈ S)
    (U : Finset K) (hp : 2*U.card < p) (cover : ∀ i ∈ S, nodes A i ∈ U)
    (hz : finrank K (cutZeroSpace K S ⊓ (volterra A).ker :
      Submodule K (Fin s → K)) ≤ z) :
    localNullityCutFloor (p-2*U.card) z ≤ s-S.card := by
  let P := cutNodalPolynomial U
  have hd : P.natDegree = U.card := natDegree_cutNodalPolynomial U
  rw [← hd] at hp ⊢
  rw [← finrank_cutZeroSpace K S]
  apply nodalColumn_localNullity_cut ho P (cutNodalPolynomial_ne_zero U) hp _
    (cutZeroSpace_volterra_le ha S hS) _ hz
  intro Q
  apply (mem_cutZeroSpace S _).mpr
  intro i hi
  have hv : P.eval (nodes A i) = 0 := cutNodalPolynomial_eval_zero (cover i hi)
  simp only [nodalColumn_apply,Polynomial.eval_mul,hv,zero_mul]

/-- Dual local-kernel cutoff of a suffix with the indicated live clocks.
Zeros in the discarded suffix do not enter hz. -/
theorem mixed_tail_active_clock_cut_of_kernel (ho : RKResearch.HasOrder p A b)
    (ha : A.IsLowerTriangular) (S : Finset (Fin s)) (hS : ∀ i ∈ S, ∀ j ≤ i, j ∈ S)
    (U : Finset K) (hp : 2*U.card < p)
    (cover : ∀ i ∉ S, b i ≠ 0 → nodes A i ∈ U)
    (hz : finrank K
      ((cutZeroSpace K S).dualAnnihilator ⊓ (volterra A).dualMap.ker :
        Submodule K (ClockCovector K s)) ≤ z) :
    localNullityCutFloor (p-2*U.card) z ≤ S.card := by
  let P := cutNodalPolynomial U
  have hd : P.natDegree = U.card := natDegree_cutNodalPolynomial U
  rw [← hd] at hp ⊢
  rw [← finrank_cutZeroSpace_annihilator K S]
  apply nodalRow_localNullity_cut ho P (cutNodalPolynomial_ne_zero U) hp _
    (cutZeroSpace_volterra_le ha S hS) _ hz
  intro Q
  apply (Submodule.mem_dualAnnihilator _).mpr
  intro v hv
  rw [nodalRow_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i ∈ S
  · rw [(mem_cutZeroSpace S _).mp hv i hi,mul_zero]
  · by_cases hb : b i = 0
    · simp only [hb,zero_mul]
    · have hw : P.eval (nodes A i) = 0 := cutNodalPolynomial_eval_zero (cover i hi hb)
      simp only [Polynomial.eval_mul,hw,zero_mul,mul_zero]

end
end RKResearch.Certified.Graded
