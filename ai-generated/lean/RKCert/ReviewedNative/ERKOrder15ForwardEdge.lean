module

public import RKCert.ReviewedNative.ForwardNodalGain
public import RKCert.ReviewedNative.OddForwardBudget
public import RKCert.ReviewedNative.NativeClockStaircase

@[expose] public section

/-! # Actual forward clock escapes at order fifteen

An explicit tableau on at most 22 stages cannot have a clock-invariant
defect space at grades 5, 6, or 7. This statement does not assume the
grade-five surplus. If that separate early surplus is available, it pins
the ranks, the intrinsic single head, and its first unmatched clock power
at the ordinary midpoint. -/
namespace RKResearch.Certified.Graded

open RKResearch Module Reverse RKCert.OneEscape
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

private theorem early_rank_window (ha : ∀ i k, i ≤ k → A i k=0) (ho : HasOrder A b 15)
    (cap : s ≤ 22) :
    4 ≤ finrank K (zeroSpace A 5) ∧
    finrank K (zeroSpace A 5) < finrank K (zeroSpace A 6) ∧
    finrank K (zeroSpace A 6) < finrank K (zeroSpace A 7) ∧
    finrank K (zeroSpace A 7) ≤ 7 := by
  have sep := coeff_separated ho (q:=7) (by decide)
  have mid := treeSpace_rank_eq_of_separation ho (q:=7) (by decide) sep
  have dim := backward_endpoint_count ha ho 7 6 (by decide) (by decide)
  exact ⟨zeroSpace_finrank ha ho (n:=4) (by decide),
    Submodule.finrank_lt_finrank_of_lt (zeroSpace_strict_of_separation ha (j:=5) sep (by decide) (by decide)),
    Submodule.finrank_lt_finrank_of_lt (zeroSpace_strict_of_separation ha (j:=6) sep (by decide) (by decide)),
    by omega⟩

/-- Entry and exit of the short midpoint each have a genuine physical
clock escape. The outgoing Hermite bound rules out invariance at 5 and 6;
the incoming bound rules it out at 7 without borrowing an eighth grade. -/
theorem order15_clock_escapes (ha : ∀ i k, i ≤ k → A i k=0) (ho : HasOrder A b 15)
    (cap : s ≤ 22) {j : ℕ} (lo : 5 ≤ j) (hi : j ≤ 7) :
    ¬ (zeroSpace A j).map (diag (nodes A)) ≤ zeroSpace A j := by
  obtain ⟨low,step₅,step₆,high⟩ := early_rank_window ha ho cap
  have sep : PolySeparated A 7 :=
    PolySeparated.of_coeff (coeff_separated ho (q:=7) (by decide))
  intro inv
  obtain z|z|z : j=5 ∨ j=6 ∨ j=7 := by omega
  · subst j
    have h := clock_invariant_outgoing ha (sep.mono (by decide : 5≤7)) le_rfl inv
    change finrank K (zeroSpace A 5)+3 ≤ finrank K (zeroSpace A 6) at h
    omega
  · subst j
    have h := clock_invariant_outgoing ha (sep.mono (by decide : 6≤7)) le_rfl inv
    change finrank K (zeroSpace A 6)+3 ≤ finrank K (zeroSpace A 7) at h
    omega
  · subst j
    have h := clock_invariant_incoming ha (j:=6) sep inv
    change finrank K (zeroSpace A 6)+3 ≤ finrank K (zeroSpace A 7) at h
    omega

/-- The actual single-head data used at the entrance to the order-15 mesh
argument. This is only the ordinary forward band; a marked endpoint is not
silently counted a second time. -/
theorem order15_head_of_grade_five (ha : ∀ i k, i ≤ k → A i k=0) (ho : HasOrder A b 15)
    (cap : s ≤ 22) (five : 5 ≤ finrank K (zeroSpace A 5)) :
    s=22 ∧ ∃ (r : ℕ) (U : Submodule K (Fin s → K)) (w : Fin s → K),
      2≤r ∧ finrank K U+r=5 ∧ U.map (diag (nodes A))≤U ∧ U≤zeroSpace A 5 ∧
      (∀ S : Submodule K (Fin s → K), S.map (diag (nodes A))≤S → S≤zeroSpace A 5 → S≤U) ∧
      (∀ n, n≤2 → zeroSpace A (5+n)=chain (diag (nodes A)) U w (r+n)) ∧
      zeroSpace A 7 ⊔ (zeroSpace A 7).map (diag (nodes A))=chain (diag (nodes A)) U w (r+3) ∧
      finrank K (zeroSpace A 7 ⊔ (zeroSpace A 7).map (diag (nodes A)) : Submodule K (Fin s→K))=8 ∧
      (diag (nodes A)^(r+2)) w∉zeroSpace A 7 := by
  obtain ⟨_,lt5,lt6,high⟩:=early_rank_window ha ho cap
  have z5 : finrank K (zeroSpace A 5)=5 := by omega
  have z6 : finrank K (zeroSpace A 6)=6 := by omega
  have z7 : finrank K (zeroSpace A 7)=7 := by omega
  have sp := coeff_separated ho (q:=7) (by decide)
  have dim := treeSpace_rank_eq_of_separation ho (q:=7) (by decide) sp
  have endCount := backward_endpoint_count ha ho 7 6 (by decide) (by decide)
  have esc := @order15_clock_escapes _ _ _ s A b ha ho cap
  have step5:=zeroSpace_clock_step_of_unit (A:=A) (n:=5) (by change finrank K (zeroSpace A 6) ≤ _; omega) (esc (j:=5) (by decide) (by decide))
  have step6:=zeroSpace_clock_step_of_unit (A:=A) (n:=6) (by change finrank K (zeroSpace A 7) ≤ _; omega) (esc (j:=6) (by decide) (by decide))
  obtain ⟨r,U,w,rpos,stable,core,big,base,_,_,hr⟩:=single_head
    (T:=diag (nodes A)) (F:=zeroSpace A 5) (by rw [←step5]; change finrank K (zeroSpace A 6) ≤ _; omega) (esc (j:=5) (by decide) (by decide))
  have sep : PolySeparated A 7 := PolySeparated.of_coeff sp
  have hU:=clock_invariant_outgoing ha (sep.mono (by decide : 5≤7)) core stable
  change finrank K U+3 ≤ finrank K (zeroSpace A 6) at hU
  have e6 : zeroSpace A 6 = chain (diag (nodes A)) U w (r+1) := by
    rw [step5,base,clock_chain_next stable rpos]
  have e7 : zeroSpace A 7 = chain (diag (nodes A)) U w (r+2) := by
    rw [step6,e6,clock_chain_next stable (by omega)]
  have edge : zeroSpace A 7 ⊔ (zeroSpace A 7).map (diag (nodes A))=
      chain (diag (nodes A)) U w (r+3) := by
    rw [e7,clock_chain_next stable (by omega)]
  have unpaid : (diag (nodes A)^(r+2)) w∉zeroSpace A 7 := by
    intro hp
    apply esc (j:=7) (by decide) (by decide)
    have same : zeroSpace A 7 ⊔ (zeroSpace A 7).map (diag (nodes A))=zeroSpace A 7 := by
      rw [edge,show r+3=(r+2)+1 by omega,chain,←e7,sup_eq_left]
      exact (Submodule.span_singleton_le_iff_mem ..).mpr hp
    exact le_sup_right.trans same.le
  refine ⟨by omega,r,U,w,by omega,by omega,stable,core,big,?_,edge,?_,unpaid⟩
  · intro n hn
    obtain rfl|rfl|rfl : n=0 ∨ n=1 ∨ n=2 := by omega
    · simpa using base
    · exact e6
    · exact e7
  · rw [edge,show r+3=(r+2)+1 by omega,chain,←e7,Submodule.finrank_sup_span_singleton unpaid,z7]

end RKResearch.Certified.Graded
