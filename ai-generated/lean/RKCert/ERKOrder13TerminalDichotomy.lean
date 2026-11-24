module
public import RKCert.ERKTerminalSteering
public import RKCert.ERKShortMidpoint

@[expose] public section

/-! # First exact branches of the order-13 equality problem
This does not exclude 19 stages. In the nonunit-clock case the genuine
18-stage order-12 prefix has live final output after reweighting.
-/
namespace RKCert.Paired.TerminalSteering
open RKCert.Paired RKCert.Paired.FiniteMidpoint RKCert.Paired.OrderTwelve
variable {K:Type*} [Field K] [CharZero K]
variable {A:Fin 19→Fin 19→K} {b:Vec K 19}

theorem order13_actual_saturation (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13) :
    Saturated A b 6 1 :=
  saturated_short (q:=6) (ε:=1) ha ho (by decide) (by decide) (by decide)

theorem order13_unit_clock_normal (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (h:nodes A (Fin.last 18)=1) :
    StrictLower (steer A b) ∧ HasTreeOrderAtLeast (steer A b) b 13 ∧
    (∀t:Tree,t.order≤13→stageWeight (steer A b) t=stageWeight A t) ∧
    nodes (steer A b)=nodes A ∧ backSeed1 (steer A b) b=0 :=
  terminal_one_steering ha ho (by decide) (order13_actual_saturation ha ho).lastLive h

theorem order13_nonunit_clock_prefix (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (h:nodes A (Fin.last 18)≠1) :
    ∃ b' : Vec K 18,HasTreeOrderAtLeast (trim A) b' 12 ∧ b' (Fin.last 17)≠0 := by
  obtain ⟨b',hb⟩:=terminal_off_one_trim ha ho (by decide) h
  refine ⟨b',hb,?_⟩
  intro hz
  have ta := trim_strict ha
  have ord : HasTreeOrderAtLeast (trim (trim A)) (fun i=>b' i.castSucc) 12 := order_trim ta hb hz
  have f := RKCert.explicit_order12_ge18_field (trim_strict ta) ord
  omega

theorem order13_terminal_cases (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13) :
    (StrictLower (steer A b) ∧ HasTreeOrderAtLeast (steer A b) b 13 ∧
      (∀t:Tree,t.order≤13→stageWeight (steer A b) t=stageWeight A t) ∧
      nodes (steer A b)=nodes A ∧ backSeed1 (steer A b) b=0) ∨
    (∃ b' : Vec K 18,HasTreeOrderAtLeast (trim A) b' 12 ∧ b' (Fin.last 17)≠0) := by
  by_cases h:nodes A (Fin.last 18)=1
  · exact Or.inl (order13_unit_clock_normal ha ho h)
  · exact Or.inr (order13_nonunit_clock_prefix ha ho h)

end RKCert.Paired.TerminalSteering
