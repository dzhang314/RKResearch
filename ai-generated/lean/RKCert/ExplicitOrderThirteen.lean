module
public import RKCert.ERKOrder13MixedCharts
public import RKCert.ExplicitPadding

@[expose] public section
/-! # An explicit ordered-field Runge–Kutta method of order 13 needs 20 stages -/
namespace RKCert
open RKCert.Paired RKCert.Paired.FiniteMidpoint RKCert.Paired.TerminalSteering
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
set_option maxHeartbeats 4200000

/-- Exact exclusion of genuine order 13 at 19 stages, with no weight-sign
or clock-distinctness hypotheses. -/
theorem explicit_order13_not_fin19 {A:Fin 19→Fin 19→K} {b:Vec K 19}
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13) : False := by
  have S:=order13_actual_saturation ha ho
  have M:=order13_fin19_prefix_margin ha ho
  obtain ⟨f4,a,r,U,w,G,C,lo,hi⟩:=order13_fin19_forces_low_fourth_defect ha ho
  rcases (show r=3∨r=4∨r=5 by omega) with rfl|rfl|rfl
  · exact marked13_rank_three_low_impossible ha ho S M C f4
  · by_cases d:qdef A∈U
    · exact marked13_rank_four_inside_impossible ha ho S M C f4 d
    · exact marked13_rank_four_outside_impossible ha ho S M C d
  · exact marked13_rank_five_impossible ha ho S M C

/-- The existing ordered-field lower bound, stated for every number of
stages. Zero-weight inactive suffix stages transport the finite witness. -/
theorem explicit_order13_ge20_orderedField {s:ℕ} {A:Fin s→Fin s→K} {b:Vec K s}
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13) : 20≤s := by
  by_contra! hs
  let m:=19-s
  have sm:s+m=19 := by dsimp [m];omega
  have ha' := ExplicitPadding.strictLower (m:=m) ha
  have ho' := ExplicitPadding.preserve_order (m:=m) ho
  have result (n:ℕ) (eq:n=19) (T:Fin n→Fin n→K) (v:Vec K n) :
      StrictLower T→HasTreeOrderAtLeast T v 13→False := by
    subst n
    exact explicit_order13_not_fin19
  exact result (s+m) sm _ _ ha' ho'

end RKCert
