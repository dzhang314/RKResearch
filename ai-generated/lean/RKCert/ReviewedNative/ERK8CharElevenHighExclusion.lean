module

public import RKCert.ReviewedNative.ERK8CharElevenHighSentinel
public import RKCert.ReviewedNative.ERK8CharElevenEarlyFiveScalars
public import RKCert.ReviewedNative.ERK8CharElevenFourHead

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Native exclusion of the entire exceptional seven-off branch
The physical center-four case uses the sentinel and late contradiction.
The physical center-five case uses the paid Newton equations, then the
existing scalar impossibility receipt. No guessed chronological or
vector-profile condition is available to the final caller. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven

open RKResearch Polynomial OneOff ERKTaggedHorizon ERK8PaidField LobattoEight RKCert.Endpoint
open scoped Classical Matrix BigOperators

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

theorem earlyNodes_two_pair (A : Matrix (Fin 10) (Fin 10) K) :
    earlyNodes A 2={nodes A 1,nodes A 2} := by
  have e : earlyRows 2=({1,2}:Finset (Fin 10)) := by decide
  unfold earlyNodes
  rw [e,Finset.image_insert,Finset.image_singleton]

theorem earlyNodes_three_triple (A : Matrix (Fin 10) (Fin 10) K) :
    earlyNodes A 3={nodes A 1,nodes A 2,nodes A 3} := by
  have e : earlyRows 3=({1,2,3}:Finset (Fin 10)) := by decide
  unfold earlyNodes
  rw [e,Finset.image_insert,Finset.image_insert,Finset.image_singleton]

theorem early_two_clock_relation
    (p : (11:K)=0) (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3)
    {theta : K} (T : ExceptionalHead A theta) (H : HighCenter A 5)
    (ratio : earlyBary A 2 (X^2)=4*earlyBary A 2 X) :
    3*nodes A 1*nodes A 2+8*(nodes A 1+nodes A 2)+1=0 := by
  let a := nodes A 1
  let c := nodes A 2
  let q : K[X] := exceptionalQuadratic
  let S := earlyNodes A 2
  let P : K[X] := X^2-C 4*X
  let v (x : K) := P.eval x/q.eval x
  let U := Lagrange.interpolate S id v
  have two : S.card=2 := earlyNodes_card seven three H (by decide)
  have Ud : U.natDegree≤1 := by
    by_cases e : U=0
    · simp [e]
    have z := (natDegree_lt_iff_degree_lt e).mpr
      (Lagrange.degree_interpolate_lt v (Set.injOn_id _) (s:=S))
    change U.natDegree < S.card at z
    omega
  have Ue (x : K) (hx : x∈S) : U.eval x=v x :=
    Lagrange.eval_interpolate_at_node v (Set.injOn_id _) hx
  have zero : earlyBary A 2 P=0 := by
    rw [show P=X^2-C 4*X from rfl,earlyBary_sub,earlyBary_Cmul,ratio,sub_self]
  have top : earlyBary A 2 P=U.coeff 1 := by
    apply earlyBary_quotient_coeff seven three T H (m:=2) (by decide) _ U (by omega)
    intro x hx
    obtain ⟨i,hi,hix⟩ := Finset.mem_image.mp hx
    have qn : q.eval x≠0 := hix ▸ exceptional_quadratic_ne_off T (earlyRows_off H (by decide) hi)
    rw [Ue x hx]
    change P.eval x=q.eval x*(P.eval x/q.eval x)
    rw [mul_div_cancel₀ _ qn]
  have u0 : U.natDegree≤0 :=
    natDegree_le_of_last_coeff_zero (k:=0) Ud (top.symm.trans zero)
  have con : U=C (U.coeff 0) := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero u0)
  have ha : a∈S := by simp [a,S,earlyNodes_two_pair]
  have hc : c∈S := by simp [c,S,earlyNodes_two_pair]
  have f := Ue a ha
  have g := Ue c hc
  rw [con,eval_C] at f g
  have n1 := earlyRows_off H (n:=2) (by decide) (by decide : (1:Fin 10)∈earlyRows 2)
  have n2 := earlyRows_off H (n:=2) (by decide) (by decide : (2:Fin 10)∈earlyRows 2)
  have qa := exceptional_quadratic_ne_off T n1
  have qc := exceptional_quadratic_ne_off T n2
  have frac : P.eval a/q.eval a=P.eval c/q.eval c := f.symm.trans g
  have cross := (div_eq_div_iff qa qc).mp frac
  have nac : a≠c := fun e => (by decide : (1:Fin 10)≠2)
    ((order8_tag_injective_of_full_count (A:=A) (by omega)).2 _ _ n1 n2 e)
  have product : (a-c)*(3*a*c+8*(a+c)+1)=0 := by
    simp only [P,exceptionalQuadratic_eval,eval_sub,eval_pow,eval_mul,eval_X,eval_C] at cross
    linear_combination cross+3*(a-c)*p
  exact (mul_eq_zero.mp product).resolve_left (sub_ne_zero.mpr nac)

theorem early_three_clock_relation
    (p : (11:K)=0) (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3)
    (H : HighCenter A 5) {beta : K} {W : K[X]}
    (shape : nodalHull (earlyNodes A 3)=C beta*(C 2+X)+exceptionalQuadratic*W) :
    -5+10*(nodes A 1+nodes A 2)-2*(nodes A 1*nodes A 2)+
      nodes A 3*(10-nodes A 1*nodes A 2-2*(nodes A 1+nodes A 2))=0 := by
  let a := nodes A 1
  let c := nodes A 2
  let d := nodes A 3
  let s := a+c
  let m := a*c
  let F := nodalHull (earlyNodes A 3)
  let q : K[X] := exceptionalQuadratic
  let R0 := -8+8*(s+d)-m*d
  let R1 := -7-(s+d)+m+d*s
  let R : K[X] := C R0+C R1*X
  let L : K[X] := C beta*(C 2+X)
  have inj := (order8_tag_injective_of_full_count (A:=A) (by omega)).2
  have ga := earlyRows_off H (n:=3) (by decide) (by decide : (1:Fin 10)∈earlyRows 3)
  have gc := earlyRows_off H (n:=3) (by decide) (by decide : (2:Fin 10)∈earlyRows 3)
  have gd := earlyRows_off H (n:=3) (by decide) (by decide : (3:Fin 10)∈earlyRows 3)
  have ac : a≠c := fun e => (by decide : (1:Fin 10)≠2) (inj _ _ ga gc e)
  have ad : a≠d := fun e => (by decide : (1:Fin 10)≠3) (inj _ _ ga gd e)
  have cd : c≠d := fun e => (by decide : (2:Fin 10)≠3) (inj _ _ gc gd e)
  have prod : F=(X-C a)*(X-C c)*(X-C d) := by
    change nodalHull (earlyNodes A 3)=_
    rw [earlyNodes_three_triple]
    change nodalHull ({a,c,d}:Finset K)=_
    unfold nodalHull
    rw [Finset.prod_insert (by simp [ac,ad]),Finset.prod_pair cd]
    ring
  have rem : F=q*(X+C (1-(s+d)))+R := by
    rw [prod]
    dsimp only [R,R0,R1,s,m,q,exceptionalQuadratic]
    simp only [map_add,map_sub,map_mul,map_neg,map_one,map_ofNat]
    ring
  change F=L+q*W at shape
  have div : q∣R-L := by
    refine ⟨W-(X+C (1-(s+d))),?_⟩
    linear_combination shape-rem
  have dr : R.natDegree≤1 := affine_degree_le _ _
  have dl : L.natDegree≤1 := by
    apply (natDegree_C_mul_le _ _).trans
    simpa only [map_one,one_mul] using affine_degree_le (2:K) 1
  have eq : R=L := sub_eq_zero.mp
    (low_quadratic_multiple_eq_zero (natDegree_sub_le_of_le dr dl) div)
  have r0 := congrArg (fun P : K[X] => P.coeff 0) eq
  have r1 := congrArg (fun P : K[X] => P.coeff 1) eq
  have e0 : R0=2*beta := by
    simp only [R,L,coeff_add,coeff_C_mul,coeff_C_zero,coeff_X_zero,mul_zero,add_zero] at r0
    linear_combination r0
  have e1 : R1=beta := by
    have c1 (u : K) : (C u).coeff 1=0 := by simp
    simpa only [R,L,coeff_add,coeff_C_mul,c1,coeff_X_one,mul_one,zero_add] using r1
  change -5+10*s-2*m+d*(10-m-2*s)=0
  dsimp only [R0,R1] at e0 e1
  linear_combination e0-2*e1-p

/-- The remaining literal center-five branch is impossible. -/
theorem seven_off_contradiction_of_center_five
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3)
    {theta : K} (T : ExceptionalHead A theta) (H : HighCenter A 5) : False := by
  obtain ⟨beta,bn,U,rem4⟩ := early_four_hull_of_center_five ha ho p seven three T H
  have c4 := first_center_five_fourth_clock ha ho p seven three T H bn rem4
  obtain ⟨W,rem3⟩ := first_center_five_three_remainder p seven three H c4 rem4
  have five : (5:K)≠0 := (ho.natCast_isUnit (n:=5) (by decide) (by decide)).ne_zero
  have ratio := first_center_five_two_measurement_ratio ha ho p seven three T H
    (mul_ne_zero five bn) rem3
  have E := early_two_clock_relation p seven three T H ratio
  have F := early_three_clock_relation p seven three H rem3
  have g1 := earlyRows_off H (n:=4) (by decide) (by decide : (1:Fin 10)∈earlyRows 4)
  have g3 := earlyRows_off H (n:=4) (by decide) (by decide : (3:Fin 10)∈earlyRows 4)
  have g4 := earlyRows_off H (n:=4) (by decide) (by decide : (4:Fin 10)∈earlyRows 4)
  have dn : nodes A 3≠-1 := by
    intro ee
    have inj := (order8_tag_injective_of_full_count (A:=A) (by omega)).2
    exact (by decide : (3:Fin 10)≠4) (inj _ _ g3 g4 (ee.trans c4.symm))
  have an := exceptional_quadratic_ne_off T g1
  rw [exceptionalQuadratic_eval] at an
  exact impossible_first_clean_five_prefix p dn an E (by linear_combination F)

/-- All seven-off candidates are now excluded over every field with
11=0, directly on the reviewed original width-ten order predicate. -/
theorem no_seven_off_char11
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0) :
    (offKnots A).card≠7 := by
  intro seven
  have three : (cleanKnots A).card=3 := by
    rcases order8_count_one_four_five_seven ha ho with h|⟨h,_⟩|⟨h,_⟩|⟨_,h⟩ <;> omega
  obtain ⟨theta,h,T,H⟩ := high_center_of_literal ha ho p seven three
  rcases high_center_four_or_five ha ho p seven three T H with e|e
  · exact seven_off_contradiction_of_center_four ha ho p seven three T (e ▸ H)
  · exact seven_off_contradiction_of_center_five ha ho p seven three T (e ▸ H)

/-- The native paid census no longer has a high-off alternative in
any field. A possible five-off branch requires characteristic eleven. -/
theorem order8_paid_only_one_four_or_five_off
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) :
    (offKnots A).card=1 ∨
      ((offKnots A).card=4 ∧ (cleanKnots A).card=5) ∨
      ((11:K)=0 ∧ (offKnots A).card=5 ∧ (cleanKnots A).card=5) := by
  by_cases p : (11:K)=0
  · rcases order8_count_one_four_five_seven ha ho with h|h|h|⟨h,_⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨p,h⟩)
    · exact (no_seven_off_char11 ha ho p h).elim
  · rcases (order8_paid_tagged_census ha ho p).2 with h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-- Over a characteristic-eleven field without a root of q, the
singleton-off branch is the only remaining alternative. -/
theorem order8_char11_nonsplit_forces_one_off
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (noRoot : ∀ x, (exceptionalQuadratic : K[X]).eval x ≠ 0) :
    (offKnots A).card=1 := by
  rcases order8_char11_nonsplit_count ha ho p noRoot with h|⟨h,_⟩
  · exact h
  · exact (no_seven_off_char11 ha ho p h).elim

end RKResearch.Certified.Graded.ERK8CharEleven

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.seven_off_contradiction_of_center_five
#print axioms RKResearch.Certified.Graded.ERK8CharEleven.no_seven_off_char11

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.order8_paid_only_one_four_or_five_off
#print axioms RKResearch.Certified.Graded.ERK8CharEleven.order8_char11_nonsplit_forces_one_off
