module

public import RKCert.ReviewedNative.NodalMaskParity
public import RKCert.ReviewedNative.NonsingularDualCensus
public import Mathlib.Algebra.Polynomial.AlgebraMap

@[expose] public section

/-! # Actual native primal and weighted dual polynomial-mask packets

The cut only uses injectivity of the physical Volterra map.  A lower
triangular matrix with nonzero diagonal provides that condition over
any field.  In particular the dual map here is *not* a weighted-transpose
inverse and needs no assumption on the individual output weights.
-/
namespace RKResearch.Certified.Graded
open Module Polynomial FiniteRootedTree
open scoped BigOperators Matrix Polynomial

noncomputable section

variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- Polynomial evaluation on the actual stage clocks. -/
def nodalColumn (A : Matrix (Fin s) (Fin s) K) : K[X] →ₗ[K] (Fin s → K) :=
  LinearMap.pi (fun i => (Polynomial.aeval (nodes A i)).toLinearMap)

@[simp]
theorem nodalColumn_apply (A : Matrix (Fin s) (Fin s) K) (Q : K[X]) (i : Fin s) :
    nodalColumn A Q i = Q.eval (nodes A i) := by
  change Polynomial.aeval (nodes A i) Q = _
  rw [Polynomial.coe_aeval_eq_eval]

/-- The actual output covector β Q(C).  Zero weights remain zero. -/
def nodalRow (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) :
    K[X] →ₗ[K] ClockCovector K s :=
  (dotProductBilin K K).comp ((diag b).comp (nodalColumn A))

theorem nodalRow_apply (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K)
    (Q : K[X]) (v : Fin s → K) :
    nodalRow A b Q v = ∑ i, b i * Q.eval (nodes A i) * v i := by
  change row (diag b (nodalColumn A Q)) v = _
  simp only [row_apply,dotProduct,diag_apply,nodalColumn_apply]

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

private theorem polyClockBand_eq_range_of_coeff {V : Type*} [AddCommGroup V] [Module K V]
    (L : K[X] →ₗ[K] V) (q : ℕ) (f : (Fin (q+1) → K) →ₗ[K] V)
    (h : ∀ Q : degreeLT K (q+1), L (Q : K[X]) = f (degreeLTEquiv K (q+1) Q)) :
    polyClockBand L q = f.range := by
  apply le_antisymm
  · rintro _ ⟨Q,hQ,rfl⟩
    exact ⟨_,(h ⟨Q,hQ⟩).symm⟩
  · rintro _ ⟨a,rfl⟩
    let e := degreeLTEquiv K (q+1)
    let Q := e.symm a
    exact ⟨Q,Q.property,(h Q).trans (congrArg f (e.apply_symm_apply a))⟩

theorem polyClockBand_nodalColumn (A : Matrix (Fin s) (Fin s) K) (q : ℕ) :
    polyClockBand (nodalColumn A) q = (coeffEval A q).range :=
  polyClockBand_eq_range_of_coeff _ _ _ (nodalColumn_eq_coeffEval A q)

theorem polyClockBand_nodalRow (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) (q : ℕ) :
    polyClockBand (nodalRow A b) q = (covClock A b q).range :=
  polyClockBand_eq_range_of_coeff _ _ _ (nodalRow_eq_covClock A b q)

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
theorem nodalColumn_paidSystem (ho : RKResearch.HasOrder p A b)
    (hR : Function.Injective (volterra A)) :
    PaidPolyClockSystem (nodalColumn A) (volterra A) (treeSpace A) p where
  step_injective := hR
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
theorem nodalRow_paidSystem (ho : RKResearch.HasOrder p A b)
    (hR : Function.Injective (volterra A)) :
    PaidPolyClockSystem (nodalRow A b) (volterra A).dualMap (dualCensusSpace A b p) p where
  step_injective := by
    intro f g h
    apply LinearMap.ext
    intro v
    obtain ⟨u,rfl⟩ := LinearMap.surjective_of_injective hR v
    exact LinearMap.congr_fun h u
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

/-- Exact masked stage-column rank, with the original reviewed tree
grade recorded. -/
theorem nodalColumn_maskedRank (ho : RKResearch.HasOrder p A b)
    (hR : Function.Injective (volterra A)) (P : K[X]) (hP : P ≠ 0)
    {m r : ℕ} (hscale : p = m+2*P.natDegree) (hr : r+1 ≤ m) :
    finrank K (maskedParityPacket (nodalColumn A) (volterra A) P m r) = parityCensus m r ∧
      maskedParityPacket (nodalColumn A) (volterra A) P m r ≤ treeSpace A (r+P.natDegree) :=
  maskedParityPacket_rank_and_le (nodalColumn_paidSystem ho hR) P hP hscale r hr

/-- Exact masked measured-covector rank in the original weighted output
flag.  All rows use the given b, including its zero and signed entries. -/
theorem nodalRow_maskedRank (ho : RKResearch.HasOrder p A b)
    (hR : Function.Injective (volterra A)) (P : K[X]) (hP : P ≠ 0)
    {m r : ℕ} (hscale : p = m+2*P.natDegree) (hr : r+1 ≤ m) :
    finrank K (maskedParityPacket (nodalRow A b) (volterra A).dualMap P m r) = parityCensus m r ∧
      maskedParityPacket (nodalRow A b) (volterra A).dualMap P m r ≤
        dualCensusSpace A b p (r+P.natDegree) :=
  maskedParityPacket_rank_and_le (nodalRow_paidSystem ho hR) P hP hscale r hr

/-- A Volterra-invariant stage subspace pays the whole effective floor
whenever it contains the masked polynomial seeds. -/
theorem nodalColumn_cut_subspace (ho : RKResearch.HasOrder p A b)
    (hR : Function.Injective (volterra A)) (P : K[X]) (hP : P ≠ 0)
    (hpos : 2*P.natDegree < p) (W : Submodule K (Fin s → K)) (hW : W.map (volterra A) ≤ W)
    (hseed : ∀ Q : K[X], nodalColumn A (P*Q) ∈ W) :
    nonsingularStageFloor (p-2*P.natDegree) ≤ finrank K W :=
  maskedParityPacket_cut_floor (nodalColumn_paidSystem ho hR) P hP hpos W hW hseed

/-- The annihilator of a Volterra-invariant stage subspace likewise
pays the effective floor if it contains the masked output seeds. -/
theorem nodalRow_cut_subspace (ho : RKResearch.HasOrder p A b)
    (hR : Function.Injective (volterra A)) (P : K[X]) (hP : P ≠ 0)
    (hpos : 2*P.natDegree < p) (W : Submodule K (Fin s → K)) (hW : W.map (volterra A) ≤ W)
    (hseed : ∀ Q : K[X], nodalRow A b (P*Q) ∈ W.dualAnnihilator) :
    nonsingularStageFloor (p-2*P.natDegree) ≤ finrank K W.dualAnnihilator := by
  apply maskedParityPacket_cut_floor (nodalRow_paidSystem ho hR) P hP hpos W.dualAnnihilator _ hseed
  rintro _ ⟨f,hf,rfl⟩
  apply (Submodule.mem_dualAnnihilator _).mpr
  intro v hv
  exact (Submodule.mem_dualAnnihilator _).mp hf _ (hW ⟨v,hv,rfl⟩)

end
end RKResearch.Certified.Graded
