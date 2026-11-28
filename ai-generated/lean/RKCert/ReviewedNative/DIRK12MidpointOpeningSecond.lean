module

public import RKCert.ReviewedNative.DIRK12MidpointOpeningModes
public import RKCert.ReviewedNative.DIRK12MidpointOpeningRead
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! The normalized two-abscissa opening row, and its literal realization
as zero-based physical row 6. Its actual low primitives are checked;
the entering quintic records exactly its paid-profile plus the unpaid
ghost excess, not a putative exact scalar sixth moment. -/

namespace RKResearch.Certified.DIRK12MidpointForward.Opening

open RKResearch Graded DIRK12MidpointGhost
open DIRK12MidpointRealInterval DirectedRatBox
open scoped Matrix BigOperators

noncomputable def ell0 (x : ℝ) : ℝ :=
  x^3*(x-1)*(5*x^2-6*x+2)/(2*db x)

noncomputable def ell1 (x : ℝ) : ℝ :=
  x*(x-1)*(2*x-1)/(2*db x)

noncomputable def wanted (x : ℝ) (k : Nat) : ℝ :=
  (x^(k+1)-rX x)/((k+1:Nat):ℝ)-kX x/((k+2:Nat):ℝ)

theorem normalized_two_read (x : ℝ) (hx : db x≠0) (m : Fin 5) :
    ell0 x+ell1 x*x^(m.val+1) =
      wanted x (m.val+1)+(if m.val=4 then kX x*eps x else 0) := by
  fin_cases m <;> norm_num [ell0,ell1,wanted,rX,kX,eps] <;>
    field_simp [hx] <;> unfold db <;> ring

/-- These are the same positive-degree cardinal reads as the original
constructor; only cancelled, not modified. -/
theorem normalized_two_cardinals (x : ℝ) (hd : db x≠0) (h0 : x≠0) (h1 : x≠1) :
    ell0 x=(wanted x 2-x*wanted x 1)/(1-x) ∧
    ell1 x=(wanted x 2-wanted x 1)/(x*(x-1)) := by
  have a := normalized_two_read x hd 0
  have b := normalized_two_read x hd 1
  have n1 : 1-x≠0 := sub_ne_zero.mpr h1.symm
  have n2 : x*(x-1)≠0 := mul_ne_zero h0 (sub_ne_zero.mpr h1)
  simp at a b
  constructor
  · rw [eq_div_iff n1]
    linear_combination b-x*a
  · rw [eq_div_iff n2]
    linear_combination b-a

@[simp] theorem realClock_second (x f : ℝ) :
    realClock x f 1=(1/2:ℝ)*x := by
  change 1-(1-((1/2:Rat):ℝ)*x)=(1/2:ℝ)*x
  push_cast
  ring

@[simp] theorem realClock_third (x f : ℝ) :
    realClock x f 2=(1/2:ℝ)*yOf x := by
  change 1-(1-((1/2:Rat):ℝ)*ratHorner yCoeffs x)=(1/2:ℝ)*yOf x
  unfold yOf
  push_cast
  ring

/-- Overwrite the second live row only. Entries after the known opening
rows are still drawn from the supplied tail data. -/
noncomputable def openingPayload (x : ℝ) (L : Fin 10 → Fin 10 → ℝ) (i j : Fin 10) : ℝ :=
  if i=1 then (if j=0 then (1/2:ℝ)*ell0 x else if j=1 then (1/2:ℝ)*ell1 x else 0)
  else L i j

noncomputable def openingFeed (x f : ℝ) (L : Fin 10 → Fin 10 → ℝ) : Feed ℝ :=
  realFeed x f (alpha x (yOf x)) (mu x (yOf x)) (nu x) (openingPayload x L)

section Actual

variable (x f : ℝ) (L : Fin 10 → Fin 10 → ℝ)
local notation "thisFeed" => openingFeed x f L

theorem literal_row6_entries :
    (thisFeed).tableau (visible 1) (visible 0)=(1/2:ℝ)*ell0 x ∧
    (thisFeed).tableau (visible 1) (visible 1)=(1/2:ℝ)*ell1 x := by
  have ne : visible (1:Fin 10)≠terminal := by decide
  refine ⟨?_,?_⟩
  · rw [(thisFeed).tableau_nonterminal_live _ _ ne]
    simp [openingFeed,realFeed,openingPayload]
  · rw [(thisFeed).tableau_nonterminal_live _ _ ne]
    simp [openingFeed,realFeed,openingPayload]

theorem row6_action (j : Nat) :
    (thisFeed).live_action 1 j = (1/2:ℝ)^(j+1)*(ell0 x+ell1 x*x^j) := by
  simp [Feed.live_action,Fin.sum_univ_succ,openingFeed,realFeed,openingPayload,mul_pow,pow_succ]
  ring

theorem row6_modes (hx : Encloses xBox x) :
    (thisFeed).mode0 1=(1/2:ℝ)*rX x ∧ (thisFeed).mode1 1=kX x := by
  obtain ⟨_,_,_,hxq,hyq,hxy⟩ := guarded_modes hx
  obtain ⟨_,hR,_,hK⟩ := modes_fit x (yOf x) hxq hyq hxy
  have e : (thisFeed).mode0 1=(1/2:ℝ)*R (alpha x (yOf x)) (mu x (yOf x)) x := by
    change realClock x f 1*(alpha x (yOf x)*leg5 (realClock x f 1)+
        mu x (yOf x)*leg6 (realClock x f 1)+
        gammaFrom (alpha x (yOf x))*leg7 (realClock x f 1)) = _
    rw [realClock_second]
    unfold R
    rw [show (1/2:ℝ)*x=x/2 by ring]
    ring
  have e' : (thisFeed).mode1 1=K (nu x) x := by
    change realClock x f 1*nu x*leg6 (realClock x f 1) = _
    rw [realClock_second,K,show (1/2:ℝ)*x=x/2 by ring]
    ring
  exact ⟨e.trans (congrArg ((1/2:ℝ)*·) hR),e'.trans hK⟩

/-- The actual physical nonterminal row passes all its paid low reads,
and has this exact entering-quintic profile for the grade-six bridge. -/
theorem row6_actual (hx : Encloses xBox x) (m : Fin 5) :
    DualSupport12.forward (thisFeed).tableau (m.val+1) (visible 1) =
      if m.val=4 then 6*(1/2:ℝ)^6*kX x*(eps x+(excess:ℝ)) else 0 := by
  obtain ⟨h0,h1⟩ := row6_modes x f L hx
  have const : (thisFeed).a=(1/2:ℝ) := rfl
  have clock1 : (thisFeed).cVisible 1=(1/2:ℝ)*x := realClock_second x f
  rw [(thisFeed).read_live 1 (by decide) m, row6_action, h0,h1,const,clock1,mul_pow,
    show m.val+1+1=m.val+2 by omega,normalized_two_read x (db_pos hx).ne' m]
  fin_cases m <;> norm_num [wanted] <;> ring

theorem row6_paid (hx : Encloses xBox x) (m : Fin 4) :
    DualSupport12.forward (thisFeed).tableau (m.val+1) (visible 1)=0 := by
  have e := row6_actual x f L hx (⟨m.val,by omega⟩ : Fin 5)
  simpa [show m.val≠4 by omega] using e

/-- 28 remaining low live primitive equations: physical rows 7 through
13, entering powers 1 through 4. -/
def OpeningRemainder : Prop :=
  ∀ (i : Fin 10), 2 ≤ i.val → visible i≠terminal →
    ∀ m : Fin 4, (thisFeed).live_budget_at i m

theorem real_opening_budget (hx : Encloses xBox x) (tail : OpeningRemainder x f L) :
    (thisFeed).LiveBudget := by
  apply real_live_budget
  intro m i ni ti
  by_cases h : i=1
  · subst i
    exact ((thisFeed).budget_at_iff 1 ti m).2 (row6_paid x f L hx m)
  · have gt : 2 ≤ i.val := by
      have i0 : i.val≠0 := fun e => ni (Fin.ext e)
      have i1 : i.val≠1 := fun e => h (Fin.ext e)
      omega
    exact tail i gt ti m

theorem real_opening_fw_primitive (hx : Encloses xBox x) (hf : Encloses fBox f)
    (hx0 : realX x=0) (hf0 : realF x f=0) (tail : OpeningRemainder x f L)
    (j : Nat) (hj : j<5) :
    DualSupport12.forward (thisFeed).tableau j ∈ forwardBand ℝ (j+1) :=
  (thisFeed).fw_primitive (real_terminal_guard x f _ _ _ _ hx hf)
    (real_ghost_weights x f _ _ _ _) (real_adjoint x f _ _ _ _ hx hf hx0 hf0)
    (real_scalar x f _ _ _ _ hx hf hx0 hf0) (real_opening_budget x f L hx tail) j hj

end Actual
end RKResearch.Certified.DIRK12MidpointForward.Opening

#print axioms RKResearch.Certified.DIRK12MidpointForward.Opening.normalized_two_read
#print axioms RKResearch.Certified.DIRK12MidpointForward.Opening.normalized_two_cardinals
#print axioms RKResearch.Certified.DIRK12MidpointForward.Opening.row6_actual
#print axioms RKResearch.Certified.DIRK12MidpointForward.Opening.real_opening_fw_primitive
