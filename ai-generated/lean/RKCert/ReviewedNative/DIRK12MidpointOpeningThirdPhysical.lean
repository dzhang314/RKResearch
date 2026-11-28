module

public import RKCert.ReviewedNative.DIRK12MidpointOpeningThird
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

@[expose] public section

/-! Physically install the third row, reusing the certified clock,
actual mode fit, and literal three-node read. -/
namespace RKResearch.Certified.DIRK12MidpointForward.Opening

open RKResearch Graded DIRK12MidpointGhost
open DIRK12MidpointRealInterval DirectedRatBox
open scoped Matrix BigOperators

/-- A paid normalized quintic read carries a separate actual physical
degree-six residual. This works for any nonterminal live row. -/
theorem physical_compensated_read (P : Feed ℝ) (i : Fin 10) (hi : visible i ≠ terminal)
    (m : Fin 5) (s r k e : ℝ)
    (hc : P.cVisible i=P.a*s) (hr : P.mode0 i=P.a*r) (hk : P.mode1 i=k)
    (paid : P.live_action i (m.val+1)=P.a^(m.val+2)*readPaid s r k e (m.val+1)) :
    DualSupport12.forward P.tableau (m.val+1) (visible i) =
      if m.val=4 then 6*P.a^6*k*(e+(excess:ℝ)) else 0 := by
  rw [P.read_live i hi m,paid,hc,hr,hk,mul_pow]
  fin_cases m <;> norm_num [readPaid] <;> ring

noncomputable def thirdPayload (x : ℝ) (L : Fin 10 → Fin 10 → ℝ) (i j : Fin 10) : ℝ :=
  if i=2 then
    if jp : j.val < 3 then (1/2:ℝ)*thirdCoeffs x ⟨j.val,jp⟩ else 0
  else L i j

noncomputable def threeFeed (x f : ℝ) (L : Fin 10 → Fin 10 → ℝ) : Feed ℝ :=
  openingFeed x f (thirdPayload x L)

section Physical

variable (x f : ℝ) (L : Fin 10 → Fin 10 → ℝ)
local notation "thisFeed" => threeFeed x f L

theorem row7_action (j : Nat) :
    (thisFeed).live_action 2 j =
      (1/2:ℝ)^(j+1)*eval3 (thirdCoeffs x) x (yOf x) j := by
  simp [Feed.live_action,Fin.sum_univ_succ,threeFeed,openingFeed,realFeed,openingPayload,
    thirdPayload,eval3,mul_pow,pow_succ]
  ring

theorem row7_modes (hx : Encloses xBox x) :
    (thisFeed).mode0 2=(1/2:ℝ)*rY x (yOf x) ∧
    (thisFeed).mode1 2=kY x (yOf x) := by
  obtain ⟨_,_,_,hq,hqy,hxy⟩ := guarded_modes hx
  obtain ⟨_,_,hR,_⟩ := modes_fit x (yOf x) hq hqy hxy
  let y := yOf x
  have e : (thisFeed).mode0 2=(1/2:ℝ)*R (alpha x y) (mu x y) y := by
    change realClock x f 2*(alpha x y*leg5 (realClock x f 2)+
        mu x y*leg6 (realClock x f 2)+gammaFrom (alpha x y)*leg7 (realClock x f 2)) = _
    rw [realClock_third]
    change (1/2:ℝ)*y*(alpha x y*leg5 ((1/2:ℝ)*y)+
        mu x y*leg6 ((1/2:ℝ)*y)+gammaFrom (alpha x y)*leg7 ((1/2:ℝ)*y))=_
    rw [show (1/2:ℝ)*y=y/2 by ring]
    unfold R
    ring
  have e' : (thisFeed).mode1 2=kY x y := by
    change realClock x f 2*nu x*leg6 (realClock x f 2)=_
    rw [realClock_third,kY,K,show (1/2:ℝ)*(yOf x)=y/2 by dsimp [y];ring]
    ring
  exact ⟨e.trans (congrArg ((1/2:ℝ)*·) hR),e'⟩

theorem row7_actual (hx : Encloses xBox x) (hx0 : realX x=0) (m : Fin 5) :
    DualSupport12.forward (thisFeed).tableau (m.val+1) (visible 2) =
      if m.val=4 then 6*(1/2:ℝ)^6*kY x (yOf x)*(eps x+(excess:ℝ)) else 0 := by
  obtain ⟨hr,hk⟩ := row7_modes x f L hx
  apply physical_compensated_read (thisFeed) 2 (by decide) m (yOf x) (rY x (yOf x))
    (kY x (yOf x)) (eps x) (realClock_third x f) hr hk
  rw [row7_action, show m.val+1+1=m.val+2 by omega,third_reads x hx hx0 m]
  rfl

theorem row7_paid (hx : Encloses xBox x) (hx0 : realX x=0) (m : Fin 4) :
    DualSupport12.forward (thisFeed).tableau (m.val+1) (visible 2)=0 := by
  have e := row7_actual x f L hx hx0 (⟨m.val,by omega⟩ : Fin 5)
  simpa [show m.val≠4 by omega] using e

/-- The remaining 24 tests are the four powers at physical live rows 8–13. -/
def ThirdRemainder : Prop :=
  ∀ (i : Fin 10), 3 ≤ i.val → visible i≠terminal →
    ∀ m : Fin 4, (thisFeed).live_budget_at i m

theorem three_opening_budget (hx : Encloses xBox x) (hx0 : realX x=0)
    (tail : ThirdRemainder x f L) : (thisFeed).LiveBudget := by
  apply real_opening_budget x f (thirdPayload x L) hx
  intro i hi ti m
  by_cases equal : i=2
  · subst i
    exact ((thisFeed).budget_at_iff 2 ti m).2 (row7_paid x f L hx hx0 m)
  · have ne : i.val≠2 := fun ee => equal (Fin.ext ee)
    exact tail i (by omega) ti m

end Physical
end RKResearch.Certified.DIRK12MidpointForward.Opening

#print axioms RKResearch.Certified.DIRK12MidpointForward.Opening.physical_compensated_read
#print axioms RKResearch.Certified.DIRK12MidpointForward.Opening.row7_actual
#print axioms RKResearch.Certified.DIRK12MidpointForward.Opening.three_opening_budget
