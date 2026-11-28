module

public import RKCert.ReviewedNative.DIRK12MidpointReverseActualTop
public import RKCert.ReviewedNative.DIRK12MidpointRealRoots
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! The exact physical real DIRK12 witness. The low band and grade-six
bridge are assembled into the generic rooted-tree theorem. Nothing
in this endpoint calls a tree enumerator or a native reflection axiom. -/
namespace RKResearch.Certified.DIRK12MidpointReverse.Actual

open RKResearch Graded DIRK12MidpointForward DIRK12MidpointForward.Opening
open DIRK12MidpointRealInterval DirectedRatBox DualSupport12VectorReplay
open scoped Matrix BigOperators

section Actual
variable (x f : ℝ)
local notation "F" => (assembled x f)
local notation "Areal" => (Feed.tableau (assembled x f))
local notation "Breal" => (Feed.b (assembled x f))
local notation "Cphys" => (nodes Areal)
local notation "Yphys" => ((1:V15 ℝ)-Cphys)
local notation "G" => (profileG x f)
local notation "H" => (profileH x f)

noncomputable def reverseGen (k : Nat) : V15 ℝ :=
  if k=0 then G else if k=1 then H else Yphys*H

noncomputable abbrev reverseBand :=
  DualSupport12VectorReplay.band (reverseGen x f)

local notation "Rev" => (reverseBand x f)

theorem G_mem (j : Nat) (hj : 3≤j) : G∈Rev j := by
  have w : 0 < width j := by unfold width; omega
  exact Submodule.subset_span ⟨(⟨0,w⟩ : Fin (width j)),by simp [reverseGen]⟩

theorem H_mem (j : Nat) (hj : 4≤j) : H∈Rev j := by
  have w : 1 < width j := by unfold width; omega
  exact Submodule.subset_span ⟨(⟨1,w⟩ : Fin (width j)),by simp [reverseGen]⟩

theorem YH_mem (j : Nat) (hj : 5≤j) : Yphys*H∈Rev j := by
  have w : 2 < width j := by unfold width; omega
  exact Submodule.subset_span ⟨(⟨2,w⟩ : Fin (width j)),by simp [reverseGen]⟩

theorem triple_mem {z : V15 ℝ} (h : ∃ a b c : ℝ, z=a • G+b • H+c • (Yphys*H)) :
    z∈Rev 5 := by
  obtain ⟨a,b,c,rfl⟩ := h
  exact (Rev 5).add_mem
    ((Rev 5).add_mem ((Rev 5).smul_mem a (G_mem x f 5 (by decide)))
      ((Rev 5).smul_mem b (H_mem x f 5 (by decide))))
    ((Rev 5).smul_mem c (YH_mem x f 5 (by decide)))

theorem reverse_band_mono (j : Nat) : Rev j ≤ Rev (j+1) :=
  band_mono (reverseGen x f) j

theorem assembled_shape :
    Matrix.IsLowerTriangular Areal ∧ Areal 0 0=0 ∧ Areal 1 1=1/16 ∧ Areal 14 14=0 := by
  have d1 := literal_second_diag x f (alpha x (yOf x)) (mu x (yOf x)) (nu x)
    (fittedPayload x f (F).live)
  have dT := literal_terminal_diag x f (alpha x (yOf x)) (mu x (yOf x)) (nu x)
    (fittedPayload x f (F).live)
  rw [←assembled_wiring x f] at d1 dT
  exact ⟨(F).isLower,(F).tableau_zero_diag,d1,dT⟩

section RootGeometry
variable (hx : Encloses xBox x) (hf : Encloses fBox f)
include hx hf

theorem reverse_band_ghost (j : Nat) (z : V15 ℝ) (hz : z∈Rev j) :
    DualSupport12.zeroAt ghostRow z := by
  intro i hi
  apply span_by_zero (reverseGen x f) j (M:=LinearMap.proj i) ?_ z hz
  intro k
  change reverseGen x f k.val i=0
  by_cases e0 : k.val=0
  · simpa [reverseGen,e0] using G_zero_ghost x f i hi
  · by_cases e1 : k.val=1
    · simpa [reverseGen,e0,e1] using H_zero_ghost x f hx hf i hi
    · simp [reverseGen,e0,e1,Pi.mul_apply,H_zero_ghost x f hx hf i hi]

theorem reverse_band_terminal (j : Nat) (z : V15 ℝ) (hz : z∈Rev j) : z terminal=0 := by
  apply span_by_zero (reverseGen x f) j (M:=LinearMap.proj terminal) ?_ z hz
  intro k
  change reverseGen x f k.val terminal=0
  by_cases e0 : k.val=0
  · simpa [reverseGen,e0] using G_zero_terminal x f
  · by_cases e1 : k.val=1
    · simpa [reverseGen,e0,e1] using H_zero_terminal x f hx hf
    · simp [reverseGen,e0,e1,Pi.mul_apply,H_zero_terminal x f hx hf]

theorem reverse_band_scalar (j m : Nat) (hjm : j+m < 12) (z : V15 ℝ) (hz : z∈Rev j) :
    row z (Cphys^m)=0 := by
  have swap (w : V15 ℝ) : row w (Cphys^m)=row (Cphys^m) w := by
    rw [row_apply,row_apply,dotProduct_comm]
  rw [swap]
  apply span_by_zero (reverseGen x f) j (M:=row (Cphys^m)) ?_ z hz
  intro k
  rw [←swap]
  have kw := k.isLt
  unfold width at kw
  by_cases e0 : k.val=0
  · simpa [reverseGen,e0] using actual_G_silent x f hx hf m
  · by_cases e1 : k.val=1
    · simpa [reverseGen,e0,e1] using actual_H_silent x f hx hf m (by omega)
    · simpa [reverseGen,e0,e1] using YH_silent x f hx hf m (by omega)

omit hx hf in
theorem reverse_band_Y (j : Nat) (hj : j < 5) (z : V15 ℝ) (hz : z∈Rev j) :
    DualSupport12.reflected Areal*z∈Rev (j+1) := by
  change diag Yphys z∈Rev (j+1)
  apply span_by_linear (reverseGen x f) j ?_ z hz
  intro k
  change Yphys*reverseGen x f k.val∈Rev (j+1)
  have kw := k.isLt
  unfold width at kw
  by_cases e : k.val=0
  · simp only [reverseGen,e,ite_true,Y_times_G]
    exact (Rev (j+1)).smul_mem _ (G_mem x f (j+1) (by omega))
  · have e1 : k.val=1 := by omega
    simp only [reverseGen,e1,Nat.one_ne_zero,ite_false,ite_true]
    exact YH_mem x f (j+1) (by omega)

section RootEquations
variable (hx0 : realX x=0) (hf0 : realF x f=0)
include hx0 hf0

theorem reverse_band_A (j : Nat) (hj : j < 5) (z : V15 ℝ) (hz : z∈Rev j) :
    mat (Matrix.transpose Areal) z∈Rev (j+1) := by
  apply span_by_linear (reverseGen x f) j ?_ z hz
  intro k
  have kw := k.isLt
  unfold width at kw
  by_cases e : k.val=0
  · simp only [reverseGen,e,ite_true,actual_pair_identity x f hx hf]
    exact (Rev (j+1)).add_mem
      ((Rev (j+1)).smul_mem _ (G_mem x f (j+1) (by omega)))
      (H_mem x f (j+1) (by omega))
  · have e1 : k.val=1 := by omega
    have j5 : j+1=5 := by omega
    simp only [reverseGen,e1,Nat.one_ne_zero,ite_false,ite_true,j5]
    exact triple_mem x f (transpose_H_three x f hx hf hx0 hf0)

theorem reverse_band_primitive (j : Nat) (hj : j < 5) :
    DualSupport12.reverse Areal Breal j∈Rev (j+1) := by
  interval_cases j
  · rw [reverse_grade1 x f hx hf hx0 hf0]
    exact (Rev _).zero_mem
  · rw [reverse_grade2 x f hx hf hx0 hf0]
    exact (Rev _).zero_mem
  · rw [reverse_grade3 x f hx hf hx0 hf0]
    exact (Rev 3).smul_mem _ (G_mem x f 3 (by decide))
  · rw [reverse_grade4 x f hx hf hx0 hf0]
    apply (Rev 4).smul_mem
    exact (Rev 4).add_mem ((Rev 4).smul_mem _ (G_mem x f 4 (by decide)))
      ((Rev 4).smul_mem _ (H_mem x f 4 (by decide)))
  · exact triple_mem x f (reverse_five_three x f hx hf hx0 hf0)

noncomputable def assembled_low_checks : DualSupport12.LowChecks Areal Breal where
  ghost := ghostRow
  fw := forwardBand ℝ
  bw := Rev
  weight_zero := by
    intro i hi
    change physicalWeight x f i=0
    rw [physicalWeight,ite_eq_left hi]
  fw_zero := fw_zero
  fw_support := fun j _ => fw_support j
  bw_support := fun j _ => reverse_band_ghost x f hx hf j
  bw_mono := fun j _ => reverse_band_mono x f j
  fw_A := (F).fw_A ((assembled_geom x f hx hf).bNZ 9) (assembled_ghost_zero x f)
    (assembled_adjoint x f hx hf hx0 hf0)
  fw_C := (F).fw_C
  fw_primitive := assembled_fw_primitive x f hx hf hx0 hf0
  bw_A := reverse_band_A x f hx hf hx0 hf0
  bw_Y := reverse_band_Y x f
  bw_primitive := reverse_band_primitive x f hx hf hx0 hf0
  bw_scalar_zero := fun j _ m hj => reverse_band_scalar x f hx hf j m hj
  bridge_A := by
    have q := real_AG5_bridge x f (alpha x (yOf x)) (mu x (yOf x)) (nu x)
      (fittedPayload x f (F).live) hx hf hx0 hf0 Rev
    rw [←assembled_wiring x f] at q
    apply q
    · intro z hz k hk
      exact reverse_band_scalar x f hx hf 5 k (by omega) z hz
    · exact reverse_band_ghost x f hx hf 5
    · exact reverse_band_terminal x f hx hf 5
  bridge_primitive :=
    actual_quintic_bridge x f hx hf hx0 hf0 Rev
      (fun z hz k hk => reverse_band_scalar x f hx hf 5 k (by omega) z hz)
      (reverse_band_ghost x f hx hf 5) (reverse_band_terminal x f hx hf 5)
  scalar := assembled_scalar x f hx hf hx0 hf0
  units := fun j _ => isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))

theorem assembled_hasOrder12 : HasOrder 12 Areal Breal :=
  DualSupport12.LowChecks.hasOrder (assembled_low_checks x f hx hf hx0 hf0)

theorem assembled_notOrder13 : ¬ HasOrder 13 Areal Breal := by
  have q := real_not_order13 x f (alpha x (yOf x)) (mu x (yOf x)) (nu x)
    (fittedPayload x f (F).live) hx hf hx0 hf0
  rw [←assembled_wiring x f] at q
  exact q

end RootEquations
end RootGeometry
end Actual

/-- An actual exact-order-12 width-15 ordinary DIRK over the reals.
The explicit origin and nonzero second diagonal exclude both ERK
and a common-diagonal SDIRK. The literal terminal is also explicit. -/
theorem exists_exact_real_dirk12 :
    ∃ (A : Matrix (Fin 15) (Fin 15) ℝ) (b : V15 ℝ),
      Matrix.IsLowerTriangular A ∧ A 0 0=0 ∧ A 1 1=1/16 ∧ A 14 14=0 ∧
        HasOrder 12 A b ∧ ¬ HasOrder 13 A b := by
  obtain ⟨x,f,hx,hf,hx0,hf0⟩ := exists_real_parameters
  obtain ⟨lower,first,second,last⟩ := assembled_shape x f
  exact ⟨(assembled x f).tableau,(assembled x f).b,lower,first,second,last,
    assembled_hasOrder12 x f hx hf hx0 hf0,assembled_notOrder13 x f hx hf hx0 hf0⟩

end RKResearch.Certified.DIRK12MidpointReverse.Actual

#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.assembled_low_checks
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.assembled_hasOrder12
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.assembled_notOrder13
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.exists_exact_real_dirk12
