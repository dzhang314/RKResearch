module

public import RKCert.ReviewedNative.DIRK12MidpointOpeningFourthPhysical
public import RKCert.ReviewedNative.PositiveCardinalRead
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! The literal positive cardinal operator of physical row 9. Five
donors pay all five positive degrees by interpolation; no additional
root relation is needed in this row. -/
namespace RKResearch.Certified.DIRK12MidpointForward.Opening

open RKResearch Graded DIRK12MidpointGhost
open DirectedRatBox DIRK12MidpointRealInterval
open scoped Matrix BigOperators Polynomial

def openingTag (i : Fin 5) : Fin 10 := ⟨i.val+2, by omega⟩

theorem openingTag_injective : Function.Injective openingTag := by
  intro i j h
  have e := congrArg Fin.val h
  apply Fin.ext
  change i.val+2=j.val+2 at e
  omega

@[simp] theorem physicalOpeningTag (i : Fin 5) :
    stageTag (visible (Fin.castAdd 5 i))=openingTag i := by
  fin_cases i <;> decide

theorem tag_not_origin (i : Fin 5) : openingTag i≠1 := by
  intro e
  have h := congrArg Fin.val e
  change i.val+2=1 at h
  omega

noncomputable def fifthNodes (x f : ℝ) (i : Fin 5) : ℝ :=
  2*(1-site x f (openingTag i))

theorem fifth_distinct {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f) :
    Function.Injective (fifthNodes x f) := by
  intro i j e
  apply openingTag_injective
  apply site_distinct hx hf
  unfold fifthNodes at e
  linear_combination (-1/2:ℝ)*e

theorem fifth_nonzero {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f)
    (i : Fin 5) : fifthNodes x f i≠0 := by
  intro e
  apply tag_not_origin i
  apply site_distinct hx hf
  change site x f (openingTag i)=1
  unfold fifthNodes at e
  linear_combination (-1/2:ℝ)*e

@[simp] theorem realClock_opening (x f : ℝ) (i : Fin 5) :
    realClock x f (Fin.castAdd 5 i)=(1/2:ℝ)*fifthNodes x f i := by
  rw [realClock,physicalOpeningTag,fifthNodes]
  ring

@[simp] theorem realClock_fifth (x f : ℝ) : realClock x f 4 = f := by
  change 1-(1-f)=f
  ring

theorem fifth_node_dictionary (x f : ℝ) :
    fifthNodes x f 0=1 ∧ fifthNodes x f 1=x ∧
    fifthNodes x f 2=yOf x ∧ fifthNodes x f 3=tOf x ∧ fifthNodes x f 4=2*f := by
  have e (i : Fin 5) : fifthNodes x f i=2*realClock x f (Fin.castAdd 5 i) := by
    linear_combination -2*realClock_opening x f i
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [e 0,show Fin.castAdd 5 (0:Fin 5)=(0:Fin 10) by decide,realClock_first]
    ring
  · rw [e 1,show Fin.castAdd 5 (1:Fin 5)=(1:Fin 10) by decide,realClock_second]
    ring
  · rw [e 2,show Fin.castAdd 5 (2:Fin 5)=(2:Fin 10) by decide,realClock_third]
    ring
  · rw [e 3,show Fin.castAdd 5 (3:Fin 5)=(3:Fin 10) by decide,realClock_fourth]
    ring
  · rw [e 4,show Fin.castAdd 5 (4:Fin 5)=(4:Fin 10) by decide,realClock_fifth]

noncomputable def fifthTarget (x f : ℝ) (j : Fin 5) : ℝ :=
  readPaid (2*f) (rAt x (2*f)) (kAt x (2*f)) (eps x) (j.val+1)

noncomputable def fifthCoeffs (x f : ℝ) : Fin 5 → ℝ :=
  PositiveCardinalRead.weights (fifthNodes x f) (fifthTarget x f)

theorem fifth_reads {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f) (m : Fin 5) :
    (∑ i : Fin 5, fifthCoeffs x f i*(fifthNodes x f i)^(m.val+1)) =
      fifthTarget x f m :=
  PositiveCardinalRead.recovers _ (fifth_distinct hx hf) (fifth_nonzero hx hf) _ m

noncomputable def fifthPayload (x f : ℝ) (L : Fin 10 → Fin 10 → ℝ) (i j : Fin 10) : ℝ :=
  if i=4 then
    if hj : j.val<5 then (1/2:ℝ)*fifthCoeffs x f ⟨j.val,hj⟩ else 0
  else L i j

noncomputable def fiveFeed (x f : ℝ) (L : Fin 10 → Fin 10 → ℝ) : Feed ℝ :=
  fourFeed x f (fifthPayload x f L)

section Physical

variable (x f : ℝ) (L : Fin 10 → Fin 10 → ℝ)
local notation "thisFeed" => fiveFeed x f L

private theorem head_lt (i : Fin 5) : ¬ (4:Fin 10)<Fin.castAdd 5 i := by
  change ¬ (4 < i.val)
  omega

private theorem tail_gt (i : Fin 5) : (4:Fin 10)<Fin.natAdd 5 i := by
  change 4<5+i.val
  omega

theorem row9_live_entry (i : Fin 5) :
    (thisFeed).live 4 (Fin.castAdd 5 i)=(1/2:ℝ)*fifthCoeffs x f i := by
  simp [fiveFeed,fourFeed,fourthPayload,threeFeed,thirdPayload,openingFeed,openingPayload,
    realFeed,fifthPayload,i.isLt]

theorem row9_actual_entry (i : Fin 5) :
    (thisFeed).tableau (visible 4) (visible (Fin.castAdd 5 i))=(1/2:ℝ)*fifthCoeffs x f i := by
  rw [(thisFeed).tableau_nonterminal_live 4 (Fin.castAdd 5 i) (by decide),
    ite_eq_right (head_lt i)]
  exact row9_live_entry x f L i

theorem row9_action (j : Nat) :
    (thisFeed).live_action 4 j =
      (1/2:ℝ)^(j+1)*(∑ i : Fin 5, fifthCoeffs x f i*(fifthNodes x f i)^j) := by
  rw [Feed.live_action,Fin.sum_univ_add (a:=5) (b:=5)]
  have z : (∑ i : Fin 5, (if (4:Fin 10)<Fin.natAdd 5 i then 0
      else (thisFeed).live 4 (Fin.natAdd 5 i))*((thisFeed).cVisible (Fin.natAdd 5 i))^j)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_left (tail_gt i),zero_mul]
  rw [z,add_zero,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [ite_eq_right (head_lt i),row9_live_entry x f L]
  change (1/2:ℝ)*fifthCoeffs x f i*(realClock x f (Fin.castAdd 5 i))^j=_
  rw [realClock_opening,mul_pow,pow_succ]
  ring

theorem row9_modes :
    (thisFeed).mode0 4=(1/2:ℝ)*rAt x (2*f) ∧
    (thisFeed).mode1 4=kAt x (2*f) := by
  let y := yOf x
  constructor
  · change realClock x f 4*(alpha x y*leg5 (realClock x f 4)+
        mu x y*leg6 (realClock x f 4)+gammaFrom (alpha x y)*leg7 (realClock x f 4))=_
    rw [realClock_fifth]
    unfold rAt R
    rw [show 2*f/2=f by ring]
    ring
  · change realClock x f 4*nu x*leg6 (realClock x f 4)=_
    rw [realClock_fifth,kAt,K,show 2*f/2=f by ring]
    ring

theorem row9_actual (hx : Encloses xBox x) (hf : Encloses fBox f) (m : Fin 5) :
    DualSupport12.forward (thisFeed).tableau (m.val+1) (visible 4)=
      if m.val=4 then 6*(1/2:ℝ)^6*kAt x (2*f)*(eps x+(excess:ℝ)) else 0 := by
  obtain ⟨hr,hk⟩ := row9_modes x f L
  have c : (thisFeed).cVisible 4=(thisFeed).a*(2*f) := by
    change realClock x f 4=(1/2:ℝ)*(2*f)
    rw [realClock_fifth]
    ring
  apply physical_compensated_read (thisFeed) 4 (by decide) m (2*f) (rAt x (2*f))
    (kAt x (2*f)) (eps x) c hr hk
  rw [row9_action,show m.val+1+1=m.val+2 by omega,fifth_reads hx hf m]
  rfl

theorem row9_paid (hx : Encloses xBox x) (hf : Encloses fBox f) (m : Fin 4) :
    DualSupport12.forward (thisFeed).tableau (m.val+1) (visible 4)=0 := by
  have h := row9_actual x f L hx hf (⟨m.val,by omega⟩ : Fin 5)
  simpa [show m.val≠4 by omega] using h

/-- The remaining 16 low tests are exactly the four positive entering
powers at physical rows 10,11,12,13. -/
def FifthRemainder : Prop :=
  ∀ (i : Fin 10), 5 ≤ i.val → visible i≠terminal →
    ∀ m : Fin 4, (thisFeed).live_budget_at i m

theorem five_opening_budget (hx : Encloses xBox x) (hf : Encloses fBox f) (hx0 : realX x=0)
    (tail : FifthRemainder x f L) : (thisFeed).LiveBudget := by
  apply four_opening_budget x f (fifthPayload x f L) hx hx0
  intro i hi ti m
  by_cases e : i=4
  · subst i
    exact ((thisFeed).budget_at_iff 4 ti m).2 (row9_paid x f L hx hf m)
  · have ne : i.val≠4 := fun h => e (Fin.ext h)
    exact tail i (by omega) ti m

end Physical
end RKResearch.Certified.DIRK12MidpointForward.Opening

#print axioms RKResearch.Certified.DIRK12MidpointForward.Opening.fifth_reads
#print axioms RKResearch.Certified.DIRK12MidpointForward.Opening.row9_actual_entry
#print axioms RKResearch.Certified.DIRK12MidpointForward.Opening.row9_actual
#print axioms RKResearch.Certified.DIRK12MidpointForward.Opening.five_opening_budget
