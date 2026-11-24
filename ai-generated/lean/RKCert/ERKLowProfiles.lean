module

public import RKCert.ERKLowThreeOff
public import RKCert.ERKLowReverseChart
public import RKCert.ERKLowReverseHermite
public import RKCert.ERKMergeRows

@[expose] public section

/-! # Actual low-order profile reductions -/
namespace RKCert.Paired
open Module
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s q : ℕ}

theorem qdef_nonzero_of_separated {A : Fin s → Fin s → K}
    (ha : StrictLower A) (hsep : Separated A q) (hq : 1 ≤ q) : qdef A ≠ 0 := by
  intro hz
  apply nodes_not_zeroSpace hsep hq
  have h1 : diag (nodes A) (1 : Vec K s) = nodes A := by ext i; simp
  have h : diag (nodes A) (1 : Vec K s) ∈ (⊥ : Submodule K (Vec K s)) := by
    apply mem_of_invariant_seed (Equiv.refl _) (mat A) (causal_mat ha) (nodes A) 1 ⊥
    · intro v hv; rw [(Submodule.mem_bot K).mp hv,map_zero]; simp
    · intro v hv; rw [(Submodule.mem_bot K).mp hv,map_zero]; simp
    · rw [←qdef_seed,hz,smul_zero]; simp
  rw [h1,Submodule.mem_bot] at h
  rw [h]
  exact (zeroSpace A q).zero_mem

omit [CharZero K] in
/-- The state count distinguishes an on feature from an off feature at
the same abscissa. It is bounded by the physical row count. -/
theorem on_off_card_le (A : Fin s → Fin s → K) :
    (onNodes A).card + (supportedNodes A (qdef A)).card ≤ s := by
  unfold onNodes supportedNodes
  apply (add_le_add Finset.card_image_le Finset.card_image_le).trans
  simpa using (Finset.card_filter_add_card_filter_not (s:=Finset.univ) (fun i => qdef A i=0)).le

theorem low_order_off_card_positive {A : Fin s → Fin s → K}
    (ha : StrictLower A) (hsep : Separated A q) (hq : 1 ≤ q) :
    0 < (supportedNodes A (qdef A)).card := by
  classical
  have hn := qdef_nonzero_of_separated ha hsep hq
  have h : ∃ i, qdef A i ≠ 0 := by
    by_contra! h; apply hn; funext i; exact h i
  obtain ⟨i,hi⟩ := h
  exact Finset.card_pos.mpr ⟨nodes A i,mem_supportedNodes.mpr ⟨i,hi,rfl⟩⟩

/-- At order eight and the ten-stage candidate, the currently checked
profile reduction leaves one, four, five, or at least seven off nodes. -/
theorem order8_off_count_chart
    {A : Fin 10 → Fin 10 → K} {b : Vec K 10}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 8) :
    let n := (supportedNodes A (qdef A)).card
    n=1 ∨ n=4 ∨ n=5 ∨ 7 ≤ n := by
  dsimp only
  obtain ⟨_,_,_,_,_,h3,h4,_,_,_,_⟩ := order8_ten_stage_chart ha ho
  have hsep : Separated A 3 := explicit_separated ha ho (by decide) (by decide)
  have hpos := low_order_off_card_positive ha hsep (by decide)
  have h2 := no_two_off_nodes ha hsep h3 h4
  have h3' := no_three_off_nodes (s:=9) ha ho (by decide) h3 h4
  have h6 : (supportedNodes A (qdef A)).card ≠ 6 := by
    intro h
    obtain ⟨P,_,_,_,_,hP⟩ := two_curve_head h3 h4 (by omega)
    have hm := five_on_of_aggregate_zero (s:=9) ha ho (by decide)
      (fun x hx => offWeight_eq_zero_from_head ho P hP (by omega) x hx)
    change 5 ≤ (onNodes A).card at hm
    have hs := on_off_card_le A
    omega
  change (supportedNodes A (qdef A)).card ≠ 3 at h3'
  omega

/-- At order nine, one is the only possible off count below four. -/
theorem order9_off_count_chart
    {A : Fin 12 → Fin 12 → K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9) :
    let n := (supportedNodes A (qdef A)).card
    n=1 ∨ 4 ≤ n := by
  dsimp only
  obtain ⟨_,h3,h4,_,_,_,_,_⟩ := order9_twelve_stage_chart ha ho
  have hsep : Separated A 3 := explicit_separated ha ho (by decide) (by decide)
  have hpos := low_order_off_card_positive ha hsep (by decide)
  have h2 := no_two_off_nodes ha hsep h3 h4
  have h3' := no_three_off_nodes (s:=11) ha ho (by decide) h3 h4
  change (supportedNodes A (qdef A)).card ≠ 3 at h3'
  omega

end RKCert.Paired

