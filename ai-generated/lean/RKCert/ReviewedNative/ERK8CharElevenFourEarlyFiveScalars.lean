module
public import RKCert.ReviewedNative.ERK8CharElevenFourEarlyMeasures
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! Literal fourth-off -1 and the earlier two-clock ratio. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven.FourOff

open RKResearch Polynomial Module OneOff ERKTaggedHorizon ERK8PaidField LobattoEight RKCert.Endpoint
open FourOffPhysical
open FiveOff (CenterPrefix)
open scoped Matrix Classical BigOperators

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

theorem early_fourth_not_in_three (distinct : EarlyOffDistinct A)
    (H : CenterPrefix A 5) : nodes A 4∉earlyNodes A 3 := by
  intro e
  obtain ⟨i,hi,hie⟩ := Finset.mem_image.mp e
  have ii := (mem_earlyRows.mp hi).2
  have m : i∈earlyRows 4 := mem_earlyRows.mpr ⟨(mem_earlyRows.mp hi).1,by omega⟩
  have h := earlyNodes_inj distinct H (n:=4) (by decide) m (by decide : (4:Fin 10)∈earlyRows 4) hie
  rw [h] at ii
  omega

theorem earlyFour_factor (distinct : EarlyOffDistinct A)
    (H : CenterPrefix A 5) :
    nodalHull (earlyNodes A 4)=(X-C (nodes A 4))*nodalHull (earlyNodes A 3) := by
  rw [earlyNodes_four_insert]
  unfold nodalHull
  exact Finset.prod_insert (early_fourth_not_in_three distinct H)

theorem earlyBary_erase_fourth
    (distinct : EarlyOffDistinct A)
    (H : CenterPrefix A 5) (P : K[X]) :
    earlyBary A 3 P=earlyBary A 4 ((X-C (nodes A 4))*P) := by
  let e := nodes A 4
  let S := earlyNodes A 3
  have en : e∉S := early_fourth_not_in_three distinct H
  have S4 : earlyNodes A 4=insert e S := earlyNodes_four_insert A
  have off (x : K) (hx : x∈S) : x≠e := fun he => en (he ▸ hx)
  have cf (x : K) (hx : x∈S) : earlyCofactor A 4 x=(x-e)*earlyCofactor A 3 x := by
    have ee : (insert e S).erase x=insert e (S.erase x) := by
      ext y
      by_cases he : y=e
      · simp [he,(off x hx).symm]
      · simp only [Finset.mem_erase,Finset.mem_insert,he,false_or]
    unfold earlyCofactor
    rw [S4,ee]
    have nn : e∉S.erase x := fun hi => en (Finset.mem_of_mem_erase hi)
    change (nodalHull (insert e (S.erase x))).eval x=(x-e)*(nodalHull (S.erase x)).eval x
    have eq : nodalHull (insert e (S.erase x))=(X-C e)*nodalHull (S.erase x) :=
      Finset.prod_insert nn
    rw [eq,eval_mul,eval_sub,eval_X,eval_C]
  change (∑ x∈S,(P.eval x/(exceptionalQuadratic : K[X]).eval x)/earlyCofactor A 3 x)=
    ∑ x∈earlyNodes A 4, (((X-C e)*P).eval x/(exceptionalQuadratic : K[X]).eval x)/earlyCofactor A 4 x
  rw [S4,Finset.sum_insert en]
  have ez : ((X-C e)*P).eval e=0 := by simp
  rw [ez,zero_div,zero_div,zero_add]
  apply Finset.sum_congr rfl
  intro x hx
  rw [cf x hx,eval_mul,eval_sub,eval_X,eval_C]
  rw [mul_div_assoc,mul_div_mul_left _ _ (sub_ne_zero.mpr (off x hx))]

theorem earlyBary_erase_fourth_pow
    (distinct : EarlyOffDistinct A)
    (H : CenterPrefix A 5) (r : ℕ) :
    earlyBary A 3 (X^r)=earlyBary A 4 (X^(r+1))-(nodes A 4)*earlyBary A 4 (X^r) := by
  rw [earlyBary_erase_fourth distinct H]
  have form : (X-C (nodes A 4))*X^r = X^(r+1)-C (nodes A 4)*X^r := by
    rw [sub_mul,pow_succ']
  rw [form,earlyBary_sub,earlyBary_Cmul]

/-- The literal fourth off clock has value -1 in the center-five branch.
The two top rows alone suffice once the paid hull remainder is known. -/
theorem first_center_five_fourth_clock
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (distinct : EarlyOffDistinct A)
    (b3 : zeroSpace A 3=band A 1) {theta : K} (T : ExceptionalHead A theta) (H : CenterPrefix A 5)
    {beta : K} (bn : beta≠0) {U : K[X]}
    (rem : nodalHull (earlyNodes A 4)=C beta*(C 3+C 9*X)+exceptionalQuadratic*U) :
    nodes A 4= -1 := by
  let L0 := earlyBary A 4 1
  let L1 := earlyBary A 4 X
  let L2 := earlyBary A 4 (X^2)
  let L3 := earlyBary A 4 (X^3)
  let e := nodes A 4
  obtain ⟨h0,h1⟩ := earlyBary_hull_receipt distinct T H (m:=4) (by decide) (by decide) bn rem
  change 3*L0+9*L1=0 at h0
  change beta*(3*L1+9*L2)+1=0 at h1
  obtain ⟨r0,r1⟩ := earlyBary_q_recurrences distinct T H (m:=4) (by decide) (by decide)
  change L2-L1+8*L0=0 at r0
  change L3-L2+8*L1=0 at r1
  have L1e : L1=4*L2 := by linear_combination 7*h0+7*r0-(7*L0+5*L1+L2)*p
  have L3e : L3=2*L2 := by linear_combination r1-8*L1e-3*L2*p
  have L2n : L2≠0 := by
    intro z
    rw [L1e,z] at h1
    simp at h1
  obtain ⟨gain,newt⟩ := early_paid_newton_two ha ho distinct b3 T H (m:=4) (Or.inr rfl)
  have z1 := newt 1 (by decide) (by decide)
  have z2 := newt 2 (by decide) (by decide)
  have v1 := earlyBary_erase_fourth_pow distinct H 1
  have v2 := earlyBary_erase_fourth_pow distinct H 2
  norm_num only [Nat.reduceAdd,Nat.reduceSub,Nat.cast_ofNat,pow_one] at z1 z2 v1 v2
  rw [v1] at z1
  rw [v2] at z2
  change 2*gain*(L2-e*L1)=L2 at z1
  change 3*gain*(L3-e*L2)=L3 at z2
  have u1 : 2*gain*(1-4*e)=1 := by
    apply mul_right_cancel₀ L2n
    linear_combination z1+2*gain*e*L1e
  have u2 : 3*gain*(2-e)=2 := by
    apply mul_right_cancel₀ L2n
    linear_combination z2-(3*gain-1)*L3e
  have ge : gain*e=1 := by linear_combination 3*u1-u2+2*gain*e*p
  have gneg : gain=-1 := by
    apply mul_left_cancel₀ (ERK8PaidField.two_ne ho)
    linear_combination u1+8*ge+p
  rw [gneg] at ge
  change e=-1
  linear_combination -ge

/-- Removing the physically determined fourth clock gives the expected
nonzero X+2 remainder for the genuine first-three hull. -/
theorem first_center_five_three_remainder
    (p : (11:K)=0) (distinct : EarlyOffDistinct A) (H : CenterPrefix A 5) (e : nodes A 4= -1)
    {beta : K} {U : K[X]}
    (rem : nodalHull (earlyNodes A 4)=C beta*(C 3+C 9*X)+exceptionalQuadratic*U) :
    ∃ W : K[X], nodalHull (earlyNodes A 3)=C (5*beta)*(C 2+X)+exceptionalQuadratic*W := by
  let D := nodalHull (earlyNodes A 3)
  let q : K[X] := exceptionalQuadratic
  let V : K[X] := C (5*beta)*(C 2+X)
  have f : nodalHull (earlyNodes A 4)=(X+1)*D := by
    rw [earlyFour_factor distinct H,e,map_neg,map_one,sub_neg_eq_add]
  have pP := polynomial_char11 p
  have v : (X+1)*V=C beta*(C 3+C 9*X)+q*C (5*beta) := by
    simp only [V,q,exceptionalQuadratic,map_mul,map_ofNat]
    linear_combination C beta*(X-3)*pP
  have m : (X+1)*(D-V)=q*(U-C (5*beta)) := by linear_combination rem-f-v
  have inv : (X+1)*(X-2)=1+q := by
    simp only [q,exceptionalQuadratic,map_ofNat]
    linear_combination -pP
  refine ⟨(X-2)*(U-C (5*beta))-(D-V),?_⟩
  change D=V+q*_
  linear_combination (X-2)*m-(D-V)*inv

/-- The native third-row Newton equations force its actual two-clock
weighted quotient to have the ratio 4. -/
theorem first_center_five_two_measurement_ratio
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (distinct : EarlyOffDistinct A)
    (b3 : zeroSpace A 3=band A 1) {theta : K} (T : ExceptionalHead A theta) (H : CenterPrefix A 5)
    {beta : K} (bn : beta≠0) {W : K[X]}
    (shape : nodalHull (earlyNodes A 3)=C beta*(C 2+X)+exceptionalQuadratic*W) :
    earlyBary A 2 (X^2)=4*earlyBary A 2 X := by
  let L0 := earlyBary A 3 1
  let L1 := earlyBary A 3 X
  let L2 := earlyBary A 3 (X^2)
  let L3 := earlyBary A 3 (X^3)
  have eq : nodalHull (earlyNodes A 3)=C beta*(C 2+C 1*X)+exceptionalQuadratic*W := by
    simpa only [map_one,one_mul] using shape
  obtain ⟨h0,h1⟩ := earlyBary_hull_receipt distinct T H (m:=3) (by decide) (by decide) bn eq
  change 2*L0+1*L1=0 at h0
  change beta*(2*L1+1*L2)+1=0 at h1
  obtain ⟨r0,r1⟩ := earlyBary_q_recurrences distinct T H (m:=3) (by decide) (by decide)
  change L2-L1+8*L0=0 at r0
  change L3-L2+8*L1=0 at r1
  have a0 : L2=L0 := by linear_combination r0+h0-L0*p
  have a1 : L3=6*L0 := by linear_combination r1+a0-8*h0+L0*p
  have L0n : L0≠0 := by
    intro z
    have t : L1=0 := by linear_combination h0-2*z
    rw [t,a0,z] at h1
    simp at h1
  obtain ⟨gamma,eqs⟩ := early_paid_newton_two ha ho distinct b3 T H (m:=3) (Or.inl rfl)
  have b0 := eqs 1 (by decide) (by decide)
  have b1 := eqs 2 (by decide) (by decide)
  norm_num only [Nat.reduceAdd,Nat.reduceSub,Nat.cast_ofNat,pow_one] at b0 b1
  change 2*gamma*earlyBary A 2 X=L2 at b0
  change 3*gamma*earlyBary A 2 (X^2)=L3 at b1
  rw [a0] at b0
  rw [a1] at b1
  have gn : gamma≠0 := fun e => L0n (by simpa [e] using b0.symm)
  have n3 : (3:K)≠0 := (ho.natCast_isUnit (n:=3) (by decide) (by decide)).ne_zero
  apply mul_left_cancel₀ (mul_ne_zero n3 gn)
  linear_combination b1-6*b0

end RKResearch.Certified.Graded.ERK8CharEleven.FourOff

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.FourOff.first_center_five_fourth_clock
#print axioms RKResearch.Certified.Graded.ERK8CharEleven.FourOff.first_center_five_two_measurement_ratio
