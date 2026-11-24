module

public import RKCert.ERKOrderNineOneOffNormalHead

@[expose] public section

/-! # The next independent clock vector and nilpotent alternative -/
namespace RKCert.Paired.OneOff
open Module

variable {K : Type*} [Field K] [CharZero K] {s : ℕ} {A : Fin s→Fin s→K}

noncomputable def deltaH (A : Fin s→Fin s→K) (d : K) : Vec K s :=
  diag (nodes A) (h A)-d • h A

omit [CharZero K] in
theorem deltaH_apply (A : Fin s→Fin s→K) (d : K) (r : Fin s) :
    deltaH A d r=(nodes A r-d)*h A r := by
  simp [deltaH,diag_apply,sub_mul]

theorem h_in_grade_three (A : Fin s→Fin s→K) : h A∈zeroSpace A 3 :=
  mat_zeroSpace_charZero A 2 (qdef_mem A)

theorem deltaH_in_grade_four (A : Fin s→Fin s→K) (d : K) : deltaH A d∈zeroSpace A 4 :=
  (zeroSpace A 4).sub_mem (diag_zeroSpace A 3 (h_in_grade_three A))
    ((zeroSpace A 4).smul_mem _ (zeroSpace_mono A (by decide) (h_in_grade_three A)))

theorem deltaH_calibration_zeros (ha : StrictLower A) {a d : K} {i j : Fin s}
    (D : ConstantAmplitude A a d i j) : deltaH A d i=0 ∧ deltaH A d j=0 := by
  constructor
  · simp [deltaH_apply,D.origin.h_first ha]
  · simp [deltaH_apply,D.node]

theorem k_calibration_zeros (ha : StrictLower A) {a d : K} {i j : Fin s}
    (D : ConstantAmplitude A a d i j) : k A i=0 ∧ k A j=0 :=
  ⟨causal_mat ha i _ (fun l li=>causal_mat ha l _ (fun n nl=>D.origin.earlier_defect n (nl.trans li))),
    causal_mat ha j _ D.first_h.earlier⟩

theorem deltaH_zero_of_small_rank (ha : StrictLower A) {a d : K} {i j : Fin s}
    (D : ConstantAmplitude A a d i j) (z : deltaH A d∈zeroSpace A 3) : deltaH A d=0 := by
  rw [D.span_three] at z
  obtain ⟨α,β,e⟩ := mem_twoSpan.mp z
  obtain ⟨zi,zj⟩ := deltaH_calibration_zeros ha D
  have ei := congrFun e i
  simp only [zi,Pi.add_apply,Pi.smul_apply,smul_eq_mul,D.origin.h_first ha,mul_zero,add_zero] at ei
  have az := (mul_eq_zero.mp ei.symm).resolve_right D.origin.g_ne
  have ej := congrFun e j
  simp only [zj,Pi.add_apply,Pi.smul_apply,smul_eq_mul,az,zero_mul,zero_add] at ej
  have bz := (mul_eq_zero.mp ej.symm).resolve_right D.first_h.nonzero
  simpa only [az,bz,zero_smul,zero_add] using e

theorem k_out_of_grade_three_if_delta_zero (ha : StrictLower A) (sep : Separated A 4)
    {a d : K} {i j : Fin s} (D : ConstantAmplitude A a d i j) (z0 : deltaH A d=0) :
    k A∉zeroSpace A 3 := by
  intro k3
  have ch : diag (nodes A) (h A)=d • h A := sub_eq_zero.mp z0
  have gm : g A∈zeroSpace A 3 := zeroSpace_mono A (by decide) (qdef_mem A)
  have hm := h_in_grade_three A
  apply not_invariant_with_g ha (sep.mono (by decide : 3≤4)) (by decide) le_rfl gm
  · intro v hv
    rw [D.span_three] at hv
    obtain ⟨c,e,rfl⟩ := mem_twoSpan.mp hv
    rw [map_add,map_smul,map_smul]
    exact (zeroSpace A 3).add_mem ((zeroSpace A 3).smul_mem _ hm)
      ((zeroSpace A 3).smul_mem _ k3)
  · intro v hv
    rw [D.span_three] at hv
    obtain ⟨c,e,rfl⟩ := mem_twoSpan.mp hv
    rw [map_add,map_smul,map_smul,D.origin.g_clock,ch]
    exact (zeroSpace A 3).add_mem ((zeroSpace A 3).smul_mem _ ((zeroSpace A 3).smul_mem _ gm))
      ((zeroSpace A 3).smul_mem _ ((zeroSpace A 3).smul_mem _ hm))

end RKCert.Paired.OneOff
