module

public import RKCert.ReviewedNative.SDIRKSixSupport
public import RKCert.ReviewedNative.SDIRKSixAlgebra
public import RKCert.ReviewedNative.SDIRKSixWeighted

@[expose] public section
/-! # Seven stages at order six for strict SDIRK

The argument uses the achieved rooted-tree order, physical triangularity and a
nonzero common diagonal only. No positivity, distinct-node, invertible weight
diagonal, real-closedness or stiff-accuracy assumption is made. -/
namespace RKResearch.Certified.Graded.SDIRKSix
open RKResearch FiniteRootedTree
open scoped FiniteRootedTree Matrix
open RKCert.Paired.SDIRK.P6 -- Pure Mathlib scalar certificate only.
variable {K : Type*} [Field K] [CharZero K]

/-- Six physical stages cannot attain all order-six rooted-tree conditions. -/
theorem order_six_six_stages_impossible {A : Matrix (Fin 6) (Fin 6) K} {b : (Fin 6 → K)} {γ:K}
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (hγ : γ≠0) : False := by
  let z:=γ⁻¹
  let B:=scaleTable z A
  let u:=B 1 0
  let v:=(nodes A 5-nodes A 4)/γ
  have hz : z≠0 := inv_ne_zero hγ
  have hf : Front B z := normal_front ho ha he hγ
  have ht : treeSpace B 4=⊤ := by
    rw [scale_treeSpace z hz A];exact order_six_grade_four_top ho ha (fun i=>he i ▸ hγ)
  have hT := third_data hf
  obtain ⟨_,_,hc5,_,_⟩:=order_six_terminal_chronology ho ha he hγ
  have h5 : nodes B 5=z-1 := by
    change nodes (scaleTable z A) 5=z-1
    rw [nodes_scaleTable]
    change γ⁻¹*nodes A 5=γ⁻¹-1
    rw [hc5];field_simp
  have h4 : nodes B 4=z-1-v := by
    change nodes (scaleTable z A) 4=z-1-v
    rw [nodes_scaleTable]
    change γ⁻¹*nodes A 4=γ⁻¹-1-(nodes A 5-nodes A 4)/γ
    rw [hc5];field_simp;ring
  have hg : seed B 4=kap v*seed B 5 := by
    change seed (scaleTable z A) 4=kap v*seed (scaleTable z A) 5
    rw [seed_scaleTable]
    change z^2*seed A 4=kap v*(z^2*seed A 5)
    have hh:=order_six_weighted_terminal_seed ho ha he hγ
    change seed A 4=kap v*seed A 5 at hh
    rw [hh];ring
  by_cases hr : B 2 1=0
  · obtain ⟨hw,hwu⟩:=zero_tap_distinct hf ht hr
    have hc := zero_algebra v hT hf.tap_ne hr hw hwu
    have hs:=first_clear hf _ (J2_clear hf hr)
    have hl:=Op.zero_word ho z u v
    rw [hs,map_zero,mul_zero] at hl
    exact zero_chart_excluded z u v hc (by linear_combination hl)
  · obtain ⟨hw,hd,hfront⟩:=nonzero_algebra v hT hf.tap_ne hr
    have hs:=H_clear hf hw hd
    have h₁:=Op.first_word ho z u v
    have h₂:=Op.second_word ho z u v
    rw [first_clear hf _ hs,map_zero,mul_zero] at h₁
    rw [second_clear hf h4 h5 _ hs,map_zero,mul_zero] at h₂
    exact nonzero_chart_excluded z u v hz hfront h₁.symm h₂.symm (terminal_algebra hf h4 h5 hg)

/-- The strict SDIRK order-six lower bound over *any characteristic-zero field*. -/
theorem seven_le_of_strict_order_six {s:ℕ} {A : Matrix (Fin s) (Fin s) K} {b : (Fin s → K)} {γ:K}
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (hγ : γ≠0) : 7≤s := by
  have h₆:=nonsingular_stageFloor_field ho ha (fun i=>he i ▸ hγ) (by decide)
  change 6≤s at h₆
  by_contra h
  have hs:s=6 := by omega
  subst s
  exact order_six_six_stages_impossible ho ha he hγ

end RKResearch.Certified.Graded.SDIRKSix

namespace RKResearch

/-- A strictly singly diagonally implicit tableau satisfying all reviewed order-six
conditions has at least seven physical stages over any characteristic-zero field. -/
theorem HasOrder.sdirk_order_six_stages_field {K : Type*} [Field K] [CharZero K] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} {γ : K}
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular)
    (hc : ∀ i, A i i = γ) (hγ : γ ≠ 0) : 7 ≤ s :=
  Certified.Graded.SDIRKSix.seven_le_of_strict_order_six ho ha hc hγ

end RKResearch
