module

public import RKCert.Dirk15MinimalCore

@[expose] public section

/-! # A true visible quartic cannot belong to the invariant core

This uses the one-dimensional image of the common core in the paid
reverse-cubic channel. No claim about coordinatewise closure of the
core, or about the support of a projected array, is required.
-/
namespace RKCert.Paired
open Module Polynomial RKCert.OneEscape
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

set_option maxHeartbeats 1400000 in
theorem order15_minimal_visible_quartic (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b) (hm : finrank K (marked A 15 4)=2)
    (h : Order15MinimalHead A b) {v : Vec K 20}
    (vh : v∈zeroSpace A 4) (vg : v∉simultaneousGhosts A b) :
    v∉h.U ∧ ∃ Q : K[X],Q≠0 ∧ Q.natDegree≤4 ∧
      (∀ i,reverseCubic A b i≠0 → v i=Q.eval (mirror A i)) ∧
      ∀ i,b i≠0 → reverseCubic A b i=0 → v i=0 := by
  have first := order15_minimal_reverse_nonlocal ha ho H
  obtain ⟨Q,dQ,prof,clean⟩ := order15_grade_four_profile ha ho H hm first vh
  let T := reverseCubic A b
  let Y := diag (mirror A)
  let L : Vec K 20 →ₗ[K] Vec K 20 := LinearMap.mulLeft K T
  let f := L.domRestrict h.U
  let V := LinearMap.range f
  have Lapp (u : Vec K 20) (i : Fin 20) : L u i=T i*u i := rfl
  have combine (hf : L v=0) : v∈simultaneousGhosts A b := by
    apply simultaneousGhosts_mem.mpr
    refine ⟨zeroSpace_first_of_row H.initial.first_zero 4 vh,fun i hi => ?_⟩
    by_cases hT : T i=0
    · exact clean i (hi.resolve_right (fun ne => ne hT)) hT
    · have e := congrFun hf i
      rw [Lapp,Pi.zero_apply] at e
      exact (mul_eq_zero.mp e).resolve_left hT
  have wne : L v≠0 := fun e => vg (combine e)
  have Qne : Q≠0 := by
    intro e
    apply wne
    ext i
    by_cases hi : T i=0
    · simp [Lapp,hi]
    · rw [Lapp,prof i hi,e,eval_zero,mul_zero,Pi.zero_apply]
  refine ⟨fun hv => ?_,Q,Qne,dQ,prof,clean⟩
  have gin : finrank K (simultaneousGhosts A b)≥1 :=
    H.initial.f3 ▸ Submodule.finrank_mono h.cubic
  have kg : (simultaneousGhosts A b).comap h.U.subtype ≤ LinearMap.ker f := by
    intro u hu
    change L u.val=0
    have e := (simultaneousGhosts_mem.mp (show u.val∈simultaneousGhosts A b from hu)).2
    ext i
    rw [Lapp,Pi.zero_apply]
    by_cases ht : T i=0
    · rw [ht,zero_mul]
    · rw [e i (Or.inr ht),mul_zero]
  have kr := Submodule.finrank_mono kg
  rw [(Submodule.comapSubtypeEquivOfLe h.ghosts).finrank_eq] at kr
  have budget := LinearMap.finrank_range_add_finrank_ker f
  have v1 : finrank K V≤1 := by
    change finrank K V+finrank K (LinearMap.ker f)=finrank K h.U at budget
    have := h.high
    omega
  have Lv : L v∈V := ⟨⟨v,hv⟩,rfl⟩
  have span : (K∙(L v))=V := Submodule.eq_of_le_of_finrank_le
    ((Submodule.span_singleton_le_iff_mem _ _).mpr Lv) (by rw [finrank_span_singleton wne]; exact v1)
  have UY : h.U.map Y≤h.U := reflected_diag_invariant_of_nodes h.maximal.2.1
  have Lcomm : L (Y v)=Y (L v) := by
    ext i
    simp only [Lapp,Y,diag_apply]
    ring
  have inV : Y (L v)∈V := ⟨⟨Y v,UY (Submodule.mem_map_of_mem hv)⟩,Lcomm⟩
  rw [←span] at inV
  obtain ⟨z,eq⟩ := Submodule.mem_span_singleton.mp inV
  let S := Clock.headSites (mirror A) T
  have sites : 5<S.card := order15_minimal_cubic_sites ha ho H first
  have er : 4<(S.erase z).card := by
    by_cases m : z∈S
    · have := Finset.card_erase_add_one m
      omega
    · rw [Finset.erase_eq_of_notMem m]
      omega
  apply Qne
  apply Polynomial.eq_of_degrees_lt_of_eval_finset_eq (S.erase z)
  · exact degree_le_natDegree.trans_lt (by exact_mod_cast (dQ.trans_lt er))
  · rw [degree_zero]
    exact WithBot.bot_lt_coe _
  · intro a am
    obtain ⟨ne,hh⟩ := Finset.mem_erase.mp am
    obtain ⟨i,mem,hi⟩ := Finset.mem_image.mp hh
    have tne : T i≠0 := (Finset.mem_filter.mp mem).2
    have e := congrFun eq i
    change (z • L v) i=Y (L v) i at e
    change z*L v i=mirror A i*L v i at e
    rw [Lapp,prof i tne,hi] at e
    have prod : (z-a)*(T i*Q.eval a)=0 := by rw [sub_mul,e,sub_self]
    rw [eval_zero]
    exact (mul_eq_zero.mp ((mul_eq_zero.mp prod).resolve_left
      (sub_ne_zero.mpr ne.symm))).resolve_left tne

end
end RKCert.Paired
