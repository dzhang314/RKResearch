module

public import RKCert.ReviewedNative.HankelPaidRestart
public import Mathlib.Data.Nat.Find

import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Keep the actual residual behind the finite Hankel tent

The older height-only wrapper is not a prerequisite. The stronger
certificate retains one monic B together with exactly the paid zeros
and the first live residual, only when it is genuinely observable. -/
namespace RKResearch.Certified.Graded.HankelNormalGapWitness

open Matrix Polynomial HankelPaidMonicBasis HankelPaidRestart
open scoped Polynomial Matrix

noncomputable section

variable {K : Type*} [Field K]

structure GapWitness (J : K[X] →ₗ[K] K) (B : K[X]) (r W g : ℕ) : Prop where
  monic : B.Monic
  degree : B.natDegree = r
  positive : 0 < g
  shape : ∀ q, q≤g → r+q≤W → nullity J (r+q)=min q (g-q)
  vanishes : ∀ j, j<r+(g-1) → j+r≤2*W-2 → residual J B j=0
  first : r+(g-1)+r≤2*W-2 → residual J B (r+(g-1))≠0

private theorem det_ne_zero_of_nullity_eq_zero (J : K[X] →ₗ[K] K) {r : ℕ}
    (zero : nullity J r=0) : (hankel J r).det≠0 := by
  have le := (hankel J r).rank_le_height
  have full : (hankel J r).rank=Fintype.card (Fin r) := by
    simp only [Fintype.card_fin]
    unfold nullity at zero
    omega
  have surj := (Matrix.mulVec_surjective_iff_rank_eq_card (M := hankel J r)).2 full
  have unit := (Matrix.mulVec_surjective_iff_isUnit (A := hankel J r)).1 surj
  exact ((Matrix.isUnit_iff_isUnit_det (hankel J r)).1 unit).ne_zero

private theorem shape_of_paid {J : K[X] →ₗ[K] K} {B : K[X]} {r W g : ℕ}
    (lead : (hankel J r).det≠0) (bm : B.Monic) (bd : B.natDegree=r)
    (positive : 0<g)
    (z : ∀ j, j<r+(g-1) → j+r≤2*W-2 → residual J B j=0)
    (v : r+(g-1)+r≤2*W-2 → residual J B (r+(g-1))≠0) :
    ∀ q, q≤g → r+q≤W → nullity J (r+q)=min q (g-q) := by
  cases g with
  | zero => omega
  | succ s =>
    intro q qg qw
    apply nullity_from_paid_residual J (s := s) qg lead bm bd
    · intro j jz jp
      apply z j
      all_goals omega
    · intro live
      have hv := v (by omega)
      simpa only [Nat.succ_sub_one] using hv

/-- An actual paid residual certificate at every normal restart. -/
theorem exists_gap_witness (J : K[X] →ₗ[K] K) {r W : ℕ}
    (rW : r<W) (hr : nullity J r=0) :
    ∃ B g, GapWitness J B r W g := by
  classical
  have lead := det_ne_zero_of_nullity_eq_zero J hr
  obtain ⟨B,bm,bd,early⟩ := exists_monic_residual J lead
  let rem := W-r
  have rp : 0<rem := by dsimp only [rem]; omega
  by_cases someLive : ∃ k, k≤2*rem-2 ∧ residual J B (r+k)≠0
  · let s := Nat.find someLive
    have spec : s≤2*rem-2 ∧ residual J B (r+s)≠0 := Nat.find_spec someLive
    have z : ∀ j, j<r+(s+1-1) → j+r≤2*W-2 → residual J B j=0 := by
      intro j jz jp
      by_cases jr : j<r
      · exact early j jr
      · let i := j-r
        have id : r+i=j := by dsimp only [i]; omega
        have before : i<s := by omega
        by_contra bad
        have hi : i≤2*rem-2 ∧ residual J B (r+i)≠0 := by
          exact ⟨by omega,by simpa only [id] using bad⟩
        exact (Nat.find_min someLive before) hi
    have v : r+(s+1-1)+r≤2*W-2 → residual J B (r+(s+1-1))≠0 := by
      intro _
      simpa only [Nat.add_sub_cancel] using spec.2
    exact ⟨B,s+1,⟨bm,bd,by omega,shape_of_paid lead bm bd (by omega) z v,z,v⟩⟩
  · let g := 2*rem
    have gp : 0<g := by dsimp only [g]; omega
    have z : ∀ j, j<r+(g-1) → j+r≤2*W-2 → residual J B j=0 := by
      intro j _ jp
      by_cases jr : j<r
      · exact early j jr
      · let i := j-r
        have id : r+i=j := by dsimp only [i]; omega
        by_contra bad
        exact someLive ⟨i,by dsimp only [rem] at *; omega,by simpa only [id] using bad⟩
    have v : r+(g-1)+r≤2*W-2 → residual J B (r+(g-1))≠0 := by
      intro impossible
      dsimp only [g,rem] at impossible
      omega
    exact ⟨B,g,⟨bm,bd,gp,shape_of_paid lead bm bd gp z v,z,v⟩⟩

variable {J : K[X] →ₗ[K] K} {B : K[X]} {r W g t : ℕ}

private theorem gap_gt_of_no_restart (h : GapWitness J B r W g) (tw : r+t≤W)
    (no : ∀ j, 0<j → j≤t → 0<nullity J (r+j)) : t<g := by
  by_contra ng
  have hz := h.shape g le_rfl (by omega)
  have hp := no g h.positive (by omega)
  rw [Nat.sub_self,Nat.min_zero] at hz
  omega

/-- A complete observed gap determines the same actual residual length. -/
theorem gap_eq_of_next_normal (h : GapWitness J B r W g) (tp : 0<t) (tw : r+t≤W)
    (no : ∀ j, 0<j → j<t → 0<nullity J (r+j)) (next : nullity J (r+t)=0) : g=t := by
  have tg : t≤g := by
    by_contra ng
    have hz := h.shape g le_rfl (by omega)
    have hp := no g h.positive (by omega)
    rw [Nat.sub_self,Nat.min_zero] at hz
    omega
  have he := h.shape t tg tw
  rw [next] at he
  by_cases hx : t≤g-t
  · rw [min_eq_left hx] at he; omega
  · rw [min_eq_right (show g-t≤t by omega)] at he; omega

/-- A positive, strictly dropped terminal height determines the true
length without needing observation of the next normal width. -/
theorem gap_eq_of_terminal_drop (h : GapWitness J B r W g) (tw : r+t≤W)
    (no : ∀ j, 0<j → j≤t → 0<nullity J (r+j)) (drop : nullity J (r+t)<t) :
    g=t+nullity J (r+t) := by
  have tg := gap_gt_of_no_restart h tw no
  have he := h.shape t tg.le tw
  have low : g-t≤t := by
    by_contra ng
    rw [min_eq_left (show t≤g-t by omega)] at he
    omega
  rw [min_eq_right low] at he
  omega

/-- In an all-rise terminal observation, only the truly available
lower residual tests are concluded; no exact longer gap is claimed. -/
theorem vanishes_of_terminal_rise (h : GapWitness J B r W g) (tw : r+t≤W)
    (no : ∀ j, 0<j → j≤t → 0<nullity J (r+j)) (rise : nullity J (r+t)=t) :
    ∀ j, j<r+(2*t-1) → j+r≤2*W-2 → residual J B j=0 := by
  have tg := gap_gt_of_no_restart h tw no
  have he := h.shape t tg.le tw
  rw [rise] at he
  have wide : 2*t≤g := by
    by_contra ng
    rw [min_eq_right (show g-t≤t by omega)] at he
    omega
  intro j jl jp
  exact h.vanishes j (by omega) jp

end
end RKResearch.Certified.Graded.HankelNormalGapWitness
