module

public import RKCert.GradeFiveCaseOne
public import RKCert.GradeFiveDependent
public import RKCert.GradeFiveCount

@[expose] public section

/-! # Reduction of the separated grade-five barrier to its normalized rows -/
namespace RKCert.Paired
open Module

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}

/-- All assumptions needed by the finite five-row dependent-case calculation
are consequences of a hypothetical deficient actual tableau. -/
theorem exists_normalized_minimal_five_eigen_profile {A : Fin s → Fin s → K}
    (ha : StrictLower A) (hsep : Separated A 5) (hR : finrank K (zeroSpace A 5)≤4) :
    ∃ (m : ℕ) (B : Fin (m+5) → Fin (m+5) → K), StrictLower B ∧ nodes B 1=1 ∧
      (∀ i, qdef B i=0 ∨ nodes B i=1 ∧ qdef B i=-((2:K)⁻¹ : K)) ∧
      (∀ i j, i < j → ∃ t : Tree, t.order≤6 ∧ stageWeight B t i≠stageWeight B t j) ∧
      zeroSpace B 3 = mixedSpan B (qdef B) (mat B (qdef B)) 0 ∧
      zeroSpace B 4 = mixedSpan B (qdef B) (mat B (qdef B)) 1 ∧
      zeroSpace B 5 = mixedSpan B (qdef B) (mat B (qdef B)) 2 := by
  obtain ⟨n,B,hb,hbs,hbr,hrows⟩ := exists_compressed_separated ha hsep
  have hn0 := treeSpace_rank_of_separated B 5 ((separated_iff_coeff B 5).mp hbs)
  have hn1 := Submodule.finrank_le (treeSpace B 5)
  change _ ≤ finrank K (Vec K n) at hn1
  rw [Module.finrank_fin_fun] at hn1
  have hn : 5≤n := by omega
  obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hn
  have hn' : n=m+5 := by omega
  clear hm
  subst n
  have hr0 := distinct_second_node hb hrows
  let r := (nodes B 1)⁻¹
  have hr : r≠0 := inv_ne_zero hr0
  let D := scaleTableau r B
  have hd : StrictLower D := scale_strict hb r
  have hs : Separated D 5 := scale_separated hr hbs
  have hnode : nodes D 1=1 := by
    change nodes (scaleTableau r B) 1=1
    rw [scale_nodes,Pi.smul_apply,smul_eq_mul]
    exact inv_mul_cancel₀ hr0
  have hDr : finrank K (zeroSpace D 5)≤4 := by
    have hEq : zeroSpace D 5 = zeroSpace B 5 := scale_zeroSpace hr B 5
    exact hEq ▸ (hbr.trans hR)
  have hDrows := no_repeat_scale hr hrows
  by_cases hdep : signal D (qdef D) 1 ∈ Submodule.span K {qdef D}
  · obtain ⟨h3,h4,h5,hbin⟩ := normalized_minimal_five_dependent hd hs hDr hnode hdep
    exact ⟨m,D,hd,hnode,hbin,hDrows,h3,h4,h5⟩
  · exact False.elim (no_minimal_five_independent hd hs hDr hDrows hdep)

end RKCert.Paired
