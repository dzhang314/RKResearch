import Lean

/-! # Shift-two weighted-nine six-off/five-clean local gates

Two independently checked components, over any core commutative field:
the exact linear-factor obstruction at the fixed shift-two Radau
quartic, and the real physical terminal duplicate-state contradiction.
The companion proof gives the weighted moment/rank bridge.
-/
namespace RKResearch.SixOffFiveGate
open Lean.Grind
variable {K : Type} [Field K]

def q4 (x : K) : K := 66*x^4-120*x^3+72*x^2-16*x+1
def qScaled (x : K) : K := 352*x^4-960*x^3+864*x^2-288*x+27
def coeffP (x : K) : K := 870740992*x^3-2210547200*x^2+1630288384*x-281812688
def coeffQ (x : K) : K := -163263936*x^3+266055840*x^2-111035232*x+10907431

theorem bezout (u : K) : coeffP u*q4 u+coeffQ u*qScaled u=12687949 := by
  unfold coeffP coeffQ q4 qScaled
  grind

theorem reflectScaled (u w : K) (r : 3*w=2*u) : 27*q4 w=qScaled u := by
  calc
    27*q4 w = 22*(3*w)^4-120*(3*w)^3+216*(3*w)^2-144*(3*w)+27 := by
      unfold q4; grind
    _ = 22*(2*u)^4-120*(2*u)^3+216*(2*u)^2-144*(2*u)+27 := by rw [r]
    _ = qScaled u := by unfold qScaled; grind

theorem linearRadauPairImpossible (u w : K) (paid : (12687949:K) ≠ 0)
    (rootU : q4 u=0) (rootW : q4 w=0) (r : 3*w=2*u) : False := by
  have h := reflectScaled u w r
  rw [rootW,Semiring.mul_zero] at h
  have b := bezout u
  rw [rootU,←h,Semiring.mul_zero,Semiring.mul_zero,Semiring.add_zero] at b
  exact paid b.symm

/-- For the monic linear head X-w, the first-clean primitive equation
is equivalent to the 2/3 root-ratio requirement, after removing u². -/
theorem linearHeadRootRatio (u w : K) (uN : u≠0)
    (chronology : u*u*(2*u-3*w)=0) : 3*w=2*u := by
  have nonzero : u*u≠0 := fun h => uN ((Field.of_mul_eq_zero h).resolve_left uN)
  have z := (Field.of_mul_eq_zero chronology).resolve_left nonzero
  grind

def lastCoordinate (i : Fin 12) : K := if i=11 then 1 else 0

/-- If the final coordinate itself is an actual state-valued column,
then its state has no other physical representative. No rows are merged. -/
theorem terminalStateUnique (clock defect : Fin 12 → K)
    (stateValued : ∀ i j, clock i=clock j → (defect i=0 ↔ defect j=0) →
      lastCoordinate (K:=K) i = lastCoordinate j)
    (i : Fin 12) (sameClock : clock i=clock 11)
    (sameTag : defect i=0 ↔ defect 11=0) : i=11 := by
  by_cases h : i=11
  · exact h
  · have e0 : lastCoordinate (K:=K) i = 0 := ite_eq_right h
    have e1 : lastCoordinate (K:=K) 11 = 1 := ite_eq_left rfl
    have one := stateValued i 11 sameClock sameTag
    exact False.elim (Field.zero_ne_one (e0.symm.trans (one.trans e1)))

private noncomputable def offMassAt (clock defect β : Fin 12 → K) (θ : K) (i : Fin 12) : K := by
  classical
  exact if clock i=θ ∧ defect i≠0 then β i else 0

/-- Literal aggregate of off weights at one physical clock, with all
twelve coordinates and the clean/off tag retained. -/
noncomputable def offMass (clock defect β : Fin 12 → K) (θ : K) : K :=
  let f := offMassAt clock defect β θ
  f 0+f 1+f 2+f 3+f 4+f 5+f 6+f 7+f 8+f 9+f 10+f 11

/-- The exact terminal contradiction once rank has put e₁₂ in the
state space and a five-clean quadrature has forced it to be off. -/
theorem offTerminalImpossible (clock defect β : Fin 12 → K)
    (stateValued : ∀ i j, clock i=clock j → (defect i=0 ↔ defect j=0) →
      lastCoordinate (K:=K) i = lastCoordinate j)
    (offLast : defect 11≠0) (liveLast : β 11≠0)
    (cancels : offMass clock defect β (clock 11)=0) : False := by
  classical
  have before (i : Fin 12) (hi : i≠11) : offMassAt clock defect β (clock 11) i=0 := by
    unfold offMassAt
    apply ite_eq_right
    intro hh
    have tagged : defect i=0 ↔ defect 11=0 := by
      exact ⟨fun q => False.elim (hh.2 q), fun q => False.elim (offLast q)⟩
    exact hi (terminalStateUnique clock defect stateValued i hh.1 tagged)
  have last : offMassAt clock defect β (clock 11) 11=β 11 := by
    unfold offMassAt
    exact ite_eq_left ⟨rfl,offLast⟩
  unfold offMass at cancels
  dsimp only at cancels
  rw [before 0 (by decide),before 1 (by decide),before 2 (by decide),
    before 3 (by decide),before 4 (by decide),before 5 (by decide),
    before 6 (by decide),before 7 (by decide),before 8 (by decide),
    before 9 (by decide),before 10 (by decide),last] at cancels
  apply liveLast
  grind

end RKResearch.SixOffFiveGate
#print axioms RKResearch.SixOffFiveGate.linearRadauPairImpossible
#print axioms RKResearch.SixOffFiveGate.linearHeadRootRatio
#print axioms RKResearch.SixOffFiveGate.terminalStateUnique
#print axioms RKResearch.SixOffFiveGate.offTerminalImpossible
