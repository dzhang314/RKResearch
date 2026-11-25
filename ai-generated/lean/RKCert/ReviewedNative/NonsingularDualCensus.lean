module

public import RKCert.ReviewedNative.NonsingularDefectDescent
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

/-! # The actual finite output probes at the nonsingular parity floor

The graded covector spaces use only the clock probes followed on their right
by powers of the physical Volterra operator. Their dimensions equal the
parity census without assuming the tableau is stage minimal or that any
individual weight is nonzero.
-/
namespace RKResearch.Certified.Graded
open FiniteRootedTree Module
open scoped BigOperators Matrix

variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

abbrev ClockCovector (K : Type*) [Field K] (s : ℕ) := Module.Dual K (Fin s → K)

def covClock (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) (q : ℕ) :
    (Fin (q+1) → K) →ₗ[K] ClockCovector K s :=
  Fintype.linearCombination K (fun j : Fin (q+1) => probe A b j.val)

private theorem covClock_apply (a : Fin (q+1) → K) (v : Fin s → K) :
    covClock A b q a v = ∑ j : Fin (q+1), a j * probe A b j.val v := by
  change (∑ j : Fin (q+1), a j • probe A b j.val) v = _
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]

private theorem probe_clock_swap (j k : ℕ) :
    probe A b j (normTree A (clockTree k)) = probe A b k (normTree A (clockTree j)) := by
  simp only [probe,row_apply,dotProduct,normTree_clockTree]
  apply Finset.sum_congr rfl
  intro i _
  ac_rfl

private theorem covClock_pair (a : Fin (q+1) → K) (k : ℕ) :
    covClock A b q a (normTree A (clockTree k)) = probe A b k (coeffEval A q a) := by
  rw [covClock_apply,coeffEval_apply,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul,smul_eq_mul,probe_clock_swap j.val k]

private theorem covClock_detect (ho : RKResearch.HasOrder p A b) {q : ℕ}
    (hp : 2*q+1 ≤ p) (a : Fin (q+1) → K)
    (hz : ∀ k : Fin (q+1), covClock A b q a (normTree A (clockTree k.val)) = 0) : a = 0 :=
  paid_coeffEval_eq_zero ho hp a (fun k => (covClock_pair a k.val).symm.trans (hz k))

private theorem covClock_range_rank (ho : RKResearch.HasOrder p A b) (q : ℕ)
    (hp : 2*q+1 ≤ p) : finrank K (covClock A b q).range = q+1 := by
  have hf : Function.Injective (covClock A b q) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro a ha
    exact covClock_detect ho hp a (fun k => by simp only [ha,LinearMap.zero_apply])
  rw [LinearMap.finrank_range_of_inj hf,Module.finrank_fin_fun]

private theorem covClock_silent (ho : RKResearch.HasOrder p A b) {q j : ℕ}
    (pay : q+j+1 ≤ p) (a : Fin (q+1) → K) {v : Fin s → K} (hv : v ∈ zeroSpace A j) :
    covClock A b q a v = 0 := by
  rw [covClock_apply]
  apply Finset.sum_eq_zero
  intro k _
  have hk := k.isLt
  rw [show probe A b k.val v = 0 from probe_zeroSpace ho (by omega) hv,mul_zero]

/-- At degree r the new rows are the pure clocks through min(r,p−1−r)
and every preceding same-parity row composed with the original Volterra map. -/
def dualCensusSpace (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) (p : ℕ) :
    ℕ → Submodule K (ClockCovector K s)
  | 0 => (covClock A b 0).range
  | 1 => (covClock A b (min 1 (p-2))).range
  | r+2 => (covClock A b (min (r+2) (p-1-(r+2)))).range ⊔
      (dualCensusSpace A b p r).map (volterra A).dualMap

theorem dualCensusSpace_silent (ho : RKResearch.HasOrder p A b) :
    ∀ d j, d+j+1 ≤ p → ∀ f ∈ dualCensusSpace A b p d,
      ∀ v ∈ zeroSpace A j, f v = 0
  | 0, j, pay, _, ⟨a,rfl⟩, v, hv => covClock_silent ho (by omega) a hv
  | 1, j, pay, _, ⟨a,rfl⟩, v, hv =>
      covClock_silent ho (by have := Nat.min_le_left 1 (p-2); omega) a hv
  | d+2, j, pay, f, hf, v, hv => by
      let q := min (d+2) (p-1-(d+2))
      change f ∈ (covClock A b q).range ⊔
        (dualCensusSpace A b p d).map (volterra A).dualMap at hf
      obtain ⟨l, ⟨a,rfl⟩, w, ⟨g,hg,rfl⟩, rfl⟩ := Submodule.mem_sup.mp hf
      have h₁ : covClock A b q a v = 0 :=
        covClock_silent ho (by dsimp [q]; omega) a hv
      have hr : volterra A v ∈ zeroSpace A (j+2) :=
        volterra_treeSpace ho j (by omega) (zeroSpace_le_treeSpace A j hv)
      have h₂ := dualCensusSpace_silent ho d (j+2) (by omega) g hg _ hr
      change covClock A b q a v + g (volterra A v) = 0
      rw [h₁,h₂,zero_add]

private theorem dualCensusRankStep (ho : RKResearch.HasOrder p A b)
    (ha : A.IsLowerTriangular) (hn : ∀ i, A i i ≠ 0) (j q : ℕ)
    (hq : q ≤ j+2) (pay : q+j+3 ≤ p) :
    finrank K (↥((covClock A b q).range ⊔
      (dualCensusSpace A b p j).map (volterra A).dualMap : Submodule K (ClockCovector K s))) =
    q+1+finrank K (dualCensusSpace A b p j) := by
  let U := (covClock A b q).range
  let W := dualCensusSpace A b p j
  let V := W.map (volterra A).dualMap
  have inj : Function.Injective (volterra A).dualMap := by
    intro f g h
    apply LinearMap.ext
    intro u
    obtain ⟨w, hw⟩ := (LinearMap.surjective_of_injective (volterra_injective ha hn)) u
    rw [← hw]
    exact LinearMap.congr_fun h w
  let e : ClockCovector K s ≃ₗ[K] ClockCovector K s :=
    LinearEquiv.ofBijective (volterra A).dualMap ⟨inj,LinearMap.surjective_of_injective inj⟩
  have hvRank : finrank K V = finrank K W := e.finrank_map_eq W
  have hUA : finrank K U = q+1 := covClock_range_rank ho q (by omega)
  have hUV : U ⊓ V = ⊥ := by
    apply le_antisymm _ bot_le
    intro f hf
    obtain ⟨hu,hv⟩ := Submodule.mem_inf.mp hf
    obtain ⟨a,hae⟩ := hu
    obtain ⟨g,hg,hge⟩ := hv
    have hzero : a = 0 := by
      apply covClock_detect ho (by omega)
      intro k
      have hk := k.isLt
      have hpow : normTree A (clockTree k.val) ∈ treeSpace A q := by
        rw [← coeffEval_single A q k]
        exact coeffEval_mem_treeSpace A q _
      have hr : volterra A (normTree A (clockTree k.val)) ∈ zeroSpace A (q+2) :=
        volterra_treeSpace ho q (by omega) hpow
      rw [hae,← hge]
      exact dualCensusSpace_silent ho j (q+2) (by omega) g hg _ hr
    rw [← hae,hzero,map_zero]
    exact (⊥ : Submodule K (ClockCovector K s)).zero_mem
  have h := Submodule.finrank_sup_add_finrank_inf_eq U V
  rw [hUV,finrank_bot,add_zero,hUA,hvRank] at h
  exact h

/-- Exact dual rank at every affordable grade, without stage-minimality
or full-weight hypotheses. This is a rank of actual iterated output rows. -/
theorem finrank_dualCensusSpace (ho : RKResearch.HasOrder p A b)
    (ha : A.IsLowerTriangular) (hn : ∀ i, A i i ≠ 0) :
    ∀ r, r+1 ≤ p → finrank K (dualCensusSpace A b p r) = parityCensus p r
  | 0, hp => covClock_range_rank ho 0 (by omega)
  | 1, hp => covClock_range_rank ho _ (by omega)
  | j+2, hp => by
      let q := min (j+2) (p-1-(j+2))
      have hs := dualCensusRankStep ho ha hn j q (Nat.min_le_left ..) (by dsimp [q]; omega)
      rw [finrank_dualCensusSpace ho ha hn j (by omega)] at hs
      exact hs

/-- Whenever the rank census fills the stage space, these finite actual
covectors span the entire dual over the original field. -/
theorem dualCensusSpace_eq_top (ho : RKResearch.HasOrder p A b)
    (ha : A.IsLowerTriangular) (hn : ∀ i, A i i ≠ 0) {r : ℕ} (hp : r+1 ≤ p)
    (h : parityCensus p r = s) : dualCensusSpace A b p r = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_dualCensusSpace ho ha hn r hp,h,Subspace.dual_finrank_eq,Module.finrank_fin_fun]

theorem order_seven_dualCensusSpace {A : Matrix (Fin 8) (Fin 8) K} {b : Fin 8 → K}
    (ho : RKResearch.HasOrder 7 A b) (ha : A.IsLowerTriangular) (hn : ∀ i, A i i ≠ 0) :
    dualCensusSpace A b 7 5 = ⊤ :=
  dualCensusSpace_eq_top ho ha hn (by decide) (by decide)

theorem order_eight_dualCensusSpace {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}
    (ho : RKResearch.HasOrder 8 A b) (ha : A.IsLowerTriangular) (hn : ∀ i, A i i ≠ 0) :
    dualCensusSpace A b 8 6 = ⊤ :=
  dualCensusSpace_eq_top ho ha hn (by decide) (by decide)

end RKResearch.Certified.Graded
