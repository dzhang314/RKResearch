module
public import RKCert.ERKOrder13TiedClosure
public import RKCert.ERKOrder13JointProfiles
public import RKCert.ERKOrder13PrefixReverse
public import RKCert.ERKOrder13TerminalDichotomy

@[expose] public section
/-! # The nonzero-first-adjoint order-thirteen equality case is impossible
This does not exclude the marked prefix with a zero first adjoint.
-/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.TerminalSteering Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
set_option maxHeartbeats 3000000

theorem full_odd_order13_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 0) : False := by
  obtain ⟨a,r,U,w,G,C⟩:=actual_chart13 ha ho S M
  have eq:a=6:=by rcases C.shape with e|⟨_,e⟩ <;> omega
  subst a
  have f4lo:=zeroSpace_finrank ha ho (n:=3) (by decide)
  change 3≤finrank K (zeroSpace A 4) at f4lo
  have f4hi:=Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separated ha S.separated (j:=4) (by decide) (by decide))
  change finrank K (zeroSpace A 4)<finrank K (zeroSpace A 5) at f4hi
  rw [S.fRank 5 le_rfl (by decide)] at f4hi
  have rTwo:=C.marked.rTwo
  have now:=C.marked.rank
  have up:r≤5:=by omega
  by_cases four:finrank K (zeroSpace A 4)=4
  · by_cases r2:r=2
    · subst r
      exact order13_full_rank_two_four_impossible ha ho S M C four
    · exact order13_full_rank_four_high_impossible ha ho S M C four (by omega)
  · have three:finrank K (zeroSpace A 4)=3:=by omega
    interval_cases r
    · exact order13_full_rank_three_two_impossible ha ho S M C three
    · exact order13_full_rank_three_three_impossible ha ho S M C three
    · by_cases inside:qdef A∈U
      · exact order13_full_rank_four_inside_impossible ha ho S M C inside
      · exact order13_full_rank_four_outside_impossible ha ho S M C inside
    · exact order13_full_rank_five_impossible ha ho S M C

section Actual
variable {A:Fin 19→Fin 19→K} {b:Vec K 19}

theorem order13_fin19_zero_first_adjoint (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13) :
    backSeed1 A b=0 := by
  by_contra h
  have S:=order13_actual_saturation ha ho
  have M := margin_short (q:=6) (ε:=1) ha ho (by decide) (by decide) S
  have rank : finrank K (back A b 0)=1 := finrank_span_singleton h
  rw [rank] at M
  exact full_odd_order13_impossible ha ho S M

theorem order13_fin19_prefix_margin (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13) :
    Margin A b 6 1 1 := by
  have S:=order13_actual_saturation ha ho
  have M := margin_short (q:=6) (ε:=1) ha ho (by decide) (by decide) S
  have z : back A b 0=⊥ := by
    change K ∙ backSeed1 A b=⊥
    rw [order13_fin19_zero_first_adjoint ha ho,Submodule.span_zero_singleton]
  rw [z,finrank_bot] at M
  exact M

/-- Actual residual scope after disposing of all full-odd cases: unit terminal
clock and a full augmented E11. This is not a 20-stage bound. -/
theorem order13_fin19_prefix_and_full_eleven (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13) :
    nodes A (Fin.last 18)=1 ∧ treePlus A 1 11=⊤ := by
  have S:=order13_actual_saturation ha ho
  have M:=order13_fin19_prefix_margin ha ho
  obtain ⟨a,r,U,w,G,C⟩:=actual_chart13 ha ho S M
  exact ⟨M.atOne (by decide),(thirteen_prefix_exact_eleven ha ho S M C).1⟩

end Actual
end RKCert.Paired.FiniteMidpoint
