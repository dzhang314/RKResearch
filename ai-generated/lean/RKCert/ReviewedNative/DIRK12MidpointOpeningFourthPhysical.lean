module

public import RKCert.ReviewedNative.DIRK12MidpointOpeningFourthGates
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! Install the literal fourth live row. Its original four-node
cardinal read has exact zero own-node coefficient, so the same row is
decoded by just three donors. All actual paid primitive reads follow. -/
namespace RKResearch.Certified.DIRK12MidpointForward.Opening

open RKResearch Graded DIRK12MidpointGhost
open DirectedRatBox DIRK12MidpointRealInterval
open scoped Matrix BigOperators

theorem paid_at_recurrence4 (x y z r k e : ℝ)
    (h : J 0 x y z=r*J 0 x y 1+k*J 1 x y 1) :
    readPaid z r k e 4 =
      (1+x+y)*readPaid z r k e 3-(x+y+x*y)*readPaid z r k e 2+
      x*y*readPaid z r k e 1 := by
  norm_num [readPaid,J] at h ⊢
  linear_combination h

theorem paid_at_recurrence5 (x y z r k e : ℝ)
    (h : J 1 x y z=r*J 1 x y 1+k*(J 2 x y 1-e)) :
    readPaid z r k e 5 =
      (1+x+y)*readPaid z r k e 4-(x+y+x*y)*readPaid z r k e 3+
      x*y*readPaid z r k e 2 := by
  norm_num [readPaid,J] at h ⊢
  linear_combination h

/-- The three donors are independent of the upper integration limit. -/
noncomputable def donorCoeffs (x y z r k e : ℝ) : Fin 3 → ℝ :=
  let M := readPaid z r k e
  weights3 x y (M 1) (M 2) (M 3)

theorem donor_paid (x y z r k e : ℝ) (hx : 0<x) (hxy : x<y) (hy : y<1)
    (q0 : J 0 x y z=r*J 0 x y 1+k*J 1 x y 1)
    (q1 : J 1 x y z=r*J 1 x y 1+k*(J 2 x y 1-e)) (m : Fin 5) :
    eval3 (donorCoeffs x y z r k e) x y (m.val+1)=readPaid z r k e (m.val+1) := by
  let V := readPaid z r k e
  let L := donorCoeffs x y z r k e
  change eval3 L x y (m.val+1)=V (m.val+1)
  obtain ⟨h1,h2,h3⟩ := weights3_paid x y (V 1) (V 2) (V 3)
    hx.ne' (hx.trans hxy).ne' (hxy.trans hy).ne hy.ne hxy.ne
  change eval3 L x y 1=V 1 at h1
  change eval3 L x y 2=V 2 at h2
  change eval3 L x y 3=V 3 at h3
  have h4 : eval3 L x y 4=V 4 := by
    have hr := recurrence3 L x y 1
    change eval3 L x y 4=(1+x+y)*eval3 L x y 3-(x+y+x*y)*eval3 L x y 2+x*y*eval3 L x y 1 at hr
    rw [hr,h1,h2,h3]
    exact (paid_at_recurrence4 x y z r k e q0).symm
  have h5 : eval3 L x y 5=V 5 := by
    have hr := recurrence3 L x y 2
    change eval3 L x y 5=(1+x+y)*eval3 L x y 4-(x+y+x*y)*eval3 L x y 3+x*y*eval3 L x y 2 at hr
    rw [hr,h2,h3,h4]
    exact (paid_at_recurrence5 x y z r k e q1).symm
  fin_cases m
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

noncomputable def fourthCoeffs (x : ℝ) : Fin 3 → ℝ :=
  donorCoeffs x (yOf x) (tOf x) (rAt x (tOf x)) (kAt x (tOf x)) (eps x)

noncomputable def fourthTargetReads (x : ℝ) : Nat → ℝ :=
  readPaid (tOf x) (rAt x (tOf x)) (kAt x (tOf x)) (eps x)

theorem fourth_reads (x : ℝ) (hx : Encloses xBox x) (hx0 : realX x=0) (m : Fin 5) :
    eval3 (fourthCoeffs x) x (yOf x) (m.val+1)=fourthTargetReads x (m.val+1) := by
  obtain ⟨h0,hxy,h1⟩ := ratios_ordered hx
  obtain ⟨f0,f1⟩ := fourth_kernel_payment hx hx0
  exact donor_paid x (yOf x) (tOf x) (rAt x (tOf x)) (kAt x (tOf x)) (eps x)
    h0 hxy h1 f0 f1 m

/-- The exact normalized positive-degree cardinal coefficient on a
fourth-degree donor set: the numerator is a routed read on T(T−a)(T−b)(T−c). -/
noncomputable def card4 (z a b c : ℝ) (M : Nat → ℝ) : ℝ :=
  (M 4-(a+b+c)*M 3+(a*b+a*c+b*c)*M 2-a*b*c*M 1)/(z*(z-a)*(z-b)*(z-c))

noncomputable def fullCardinals4 (x y t : ℝ) (M : Nat → ℝ) (j : Fin 4) : ℝ :=
  if j=0 then card4 1 x y t M
  else if j=1 then card4 x 1 y t M
  else if j=2 then card4 y 1 x t M
  else card4 t 1 x y M

theorem cardDenoms (x y t : ℝ) (hx : 0<x) (hxt : x<t) (hty : t<y) (hy : y<1) :
    (1-x)*(1-y)*(1-t)≠0 ∧
    x*(x-1)*(x-y)*(x-t)≠0 ∧
    y*(y-1)*(y-x)*(y-t)≠0 ∧
    t*(t-1)*(t-x)*(t-y)≠0 := by
  have hxy := hxt.trans hty
  have ht1 := hty.trans hy
  have hx1 := hxy.trans hy
  exact ⟨mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hx1.ne.symm)
      (sub_ne_zero.mpr hy.ne.symm)) (sub_ne_zero.mpr ht1.ne.symm),
    mul_ne_zero (mul_ne_zero (mul_ne_zero hx.ne' (sub_ne_zero.mpr hx1.ne))
      (sub_ne_zero.mpr hxy.ne)) (sub_ne_zero.mpr hxt.ne),
    mul_ne_zero (mul_ne_zero (mul_ne_zero (hx.trans hxy).ne' (sub_ne_zero.mpr hy.ne))
      (sub_ne_zero.mpr hxy.ne.symm)) (sub_ne_zero.mpr hty.ne.symm),
    mul_ne_zero (mul_ne_zero (mul_ne_zero (hx.trans hxt).ne' (sub_ne_zero.mpr ht1.ne))
      (sub_ne_zero.mpr hxt.ne.symm)) (sub_ne_zero.mpr hty.ne)⟩

theorem card4_eval3 (x y t : ℝ) (p : Fin 3 → ℝ)
    (hx : 0<x) (hxt : x<t) (hty : t<y) (hy : y<1) (j : Fin 4) :
    fullCardinals4 x y t (eval3 p x y) j = if hj : j.val<3 then p ⟨j.val,hj⟩ else 0 := by
  obtain ⟨d0,d1,d2,d3⟩ := cardDenoms x y t hx hxt hty hy
  fin_cases j
  · change card4 1 x y t (eval3 p x y)=p 0
    unfold card4 eval3
    have d : (1:ℝ)*(1-x)*(1-y)*(1-t)≠0 := by simpa using d0
    apply (div_eq_iff d).2
    ring
  · change card4 x 1 y t (eval3 p x y)=p 1
    unfold card4 eval3
    apply (div_eq_iff d1).2
    ring
  · change card4 y 1 x t (eval3 p x y)=p 2
    unfold card4 eval3
    apply (div_eq_iff d2).2
    ring
  · change card4 t 1 x y (eval3 p x y)=0
    unfold card4 eval3
    apply (div_eq_iff d3).2
    ring

theorem card_fidelity (x : ℝ) (hx : Encloses xBox x) (hx0 : realX x=0) (j : Fin 4) :
    fullCardinals4 x (yOf x) (tOf x) (fourthTargetReads x) j =
      if hj : j.val<3 then fourthCoeffs x ⟨j.val,hj⟩ else 0 := by
  obtain ⟨h0,hxt,hty,h1⟩ := fourth_clocks_ordered hx
  have m1 : fourthTargetReads x 1=eval3 (fourthCoeffs x) x (yOf x) 1 :=
    (fourth_reads x hx hx0 0).symm
  have m2 : fourthTargetReads x 2=eval3 (fourthCoeffs x) x (yOf x) 2 :=
    (fourth_reads x hx hx0 1).symm
  have m3 : fourthTargetReads x 3=eval3 (fourthCoeffs x) x (yOf x) 3 :=
    (fourth_reads x hx hx0 2).symm
  have m4 : fourthTargetReads x 4=eval3 (fourthCoeffs x) x (yOf x) 4 :=
    (fourth_reads x hx hx0 3).symm
  have h := card4_eval3 x (yOf x) (tOf x) (fourthCoeffs x) h0 hxt hty h1 j
  simpa only [fullCardinals4,card4,m1,m2,m3,m4] using h

@[simp] theorem realClock_fourth (x f : ℝ) :
    realClock x f 3=(1/2:ℝ)*tOf x := by
  change 1-(1-((1/2:Rat):ℝ)*ratHorner tCoeffs x)=(1/2:ℝ)*tOf x
  unfold tOf
  push_cast
  ring

noncomputable def fourthPayload (x : ℝ) (L : Fin 10 → Fin 10 → ℝ) (i j : Fin 10) : ℝ :=
  if i=3 then
    if hj : j.val<3 then (1/2:ℝ)*fourthCoeffs x ⟨j.val,hj⟩ else 0
  else L i j

noncomputable def fourFeed (x f : ℝ) (L : Fin 10 → Fin 10 → ℝ) : Feed ℝ :=
  threeFeed x f (fourthPayload x L)

section Physical

variable (x f : ℝ) (L : Fin 10 → Fin 10 → ℝ)
local notation "thisFeed" => fourFeed x f L

theorem row8_actual_entry (j : Fin 4) (hx : Encloses xBox x) (hx0 : realX x=0) :
    (thisFeed).tableau (visible 3) (visible (Fin.castAdd 6 j)) =
      (1/2:ℝ)*fullCardinals4 x (yOf x) (tOf x) (fourthTargetReads x) j := by
  rw [(thisFeed).tableau_nonterminal_live 3 (Fin.castAdd 6 j) (by decide), card_fidelity x hx hx0 j]
  fin_cases j <;> simp [fourFeed,threeFeed,thirdPayload,openingFeed,openingPayload,realFeed,fourthPayload]

theorem row8_zero_diagonal :
    (thisFeed).tableau (visible 3) (visible 3)=0 := by
  rw [(thisFeed).tableau_nonterminal_live 3 3 (by decide)]
  simp [fourFeed,threeFeed,thirdPayload,openingFeed,openingPayload,realFeed,fourthPayload]

theorem row8_action (j : Nat) :
    (thisFeed).live_action 3 j =
      (1/2:ℝ)^(j+1)*eval3 (fourthCoeffs x) x (yOf x) j := by
  simp [Feed.live_action,Fin.sum_univ_succ,fourFeed,threeFeed,openingFeed,realFeed,
    openingPayload,thirdPayload,fourthPayload,eval3,mul_pow,pow_succ]
  ring

theorem row8_modes :
    (thisFeed).mode0 3=(1/2:ℝ)*rAt x (tOf x) ∧
    (thisFeed).mode1 3=kAt x (tOf x) := by
  let y := yOf x
  let t := tOf x
  constructor
  · change realClock x f 3*(alpha x y*leg5 (realClock x f 3)+
        mu x y*leg6 (realClock x f 3)+gammaFrom (alpha x y)*leg7 (realClock x f 3))=_
    rw [realClock_fourth]
    change (1/2:ℝ)*t*(alpha x y*leg5 ((1/2:ℝ)*t)+
        mu x y*leg6 ((1/2:ℝ)*t)+gammaFrom (alpha x y)*leg7 ((1/2:ℝ)*t))=_
    rw [show (1/2:ℝ)*t=t/2 by ring]
    unfold rAt R
    ring
  · change realClock x f 3*nu x*leg6 (realClock x f 3)=_
    rw [realClock_fourth,kAt,K,show (1/2:ℝ)*(tOf x)=t/2 by dsimp [t];ring]
    ring

theorem row8_actual (hx : Encloses xBox x) (hx0 : realX x=0) (m : Fin 5) :
    DualSupport12.forward (thisFeed).tableau (m.val+1) (visible 3)=
      if m.val=4 then 6*(1/2:ℝ)^6*kAt x (tOf x)*(eps x+(excess:ℝ)) else 0 := by
  obtain ⟨hr,hk⟩ := row8_modes x f L
  apply physical_compensated_read (thisFeed) 3 (by decide) m (tOf x) (rAt x (tOf x))
    (kAt x (tOf x)) (eps x) (realClock_fourth x f) hr hk
  rw [row8_action,show m.val+1+1=m.val+2 by omega,fourth_reads x hx hx0 m]
  rfl

theorem row8_paid (hx : Encloses xBox x) (hx0 : realX x=0) (m : Fin 4) :
    DualSupport12.forward (thisFeed).tableau (m.val+1) (visible 3)=0 := by
  have h := row8_actual x f L hx hx0 (⟨m.val,by omega⟩ : Fin 5)
  simpa [show m.val≠4 by omega] using h

/-- The remaining 20 tests: four positive powers at physical rows 9–13. -/
def FourthRemainder : Prop :=
  ∀ (i : Fin 10), 4 ≤ i.val → visible i≠terminal →
    ∀ m : Fin 4, (thisFeed).live_budget_at i m

theorem four_opening_budget (hx : Encloses xBox x) (hx0 : realX x=0)
    (tail : FourthRemainder x f L) : (thisFeed).LiveBudget := by
  apply three_opening_budget x f (fourthPayload x L) hx hx0
  intro i hi ti m
  by_cases e : i=3
  · subst i
    exact ((thisFeed).budget_at_iff 3 ti m).2 (row8_paid x f L hx hx0 m)
  · have ne : i.val≠3 := fun h => e (Fin.ext h)
    exact tail i (by omega) ti m

end Physical
end RKResearch.Certified.DIRK12MidpointForward.Opening

#print axioms RKResearch.Certified.DIRK12MidpointForward.Opening.card_fidelity
#print axioms RKResearch.Certified.DIRK12MidpointForward.Opening.row8_actual_entry
#print axioms RKResearch.Certified.DIRK12MidpointForward.Opening.row8_zero_diagonal
#print axioms RKResearch.Certified.DIRK12MidpointForward.Opening.row8_actual
#print axioms RKResearch.Certified.DIRK12MidpointForward.Opening.four_opening_budget
