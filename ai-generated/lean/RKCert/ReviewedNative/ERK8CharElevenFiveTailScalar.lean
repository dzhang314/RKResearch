module

public import RKCert.ReviewedNative.ERK8CharElevenFiveTailPhysical

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! The two physical five-off tail orders force the published scalar
contradictions. No coefficient order, extra reverse profile, or
declared value of a clean weight is needed. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven.FiveOff

open RKResearch Polynomial Module OneOff ERKTaggedHorizon ERK8PaidField LobattoEight RKCert.Endpoint
open RKResearch.Certified.Graded.ERK8CharEleven
open scoped Classical Matrix BigOperators

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

def firstFourOffRows : Finset (Fin 10) := {5,1,2,3}

theorem firstFourOffRows_image (A : Matrix (Fin 10) (Fin 10) K) :
    firstFourOffRows.image (nodes A)=earlyFourClocks A := by
  simp [firstFourOffRows,earlyFourClocks,earlyThreeClocks]

theorem bulkClock_insertions (A : Matrix (Fin 10) (Fin 10) K) :
    bulkClocks A=insert (nodes A 7) (insert (nodes A 8) (insert (nodes A 6) (earlyFourClocks A))) ∧
    bulkClocks A=insert (nodes A 8) (insert (nodes A 7) (insert (nodes A 6) (earlyFourClocks A))) := by
  have e : bulkRows=insert (7:Fin 10) (insert 8 (insert 6 firstFourOffRows)) := by decide
  have one : bulkClocks A=insert (nodes A 7) (insert (nodes A 8) (insert (nodes A 6) (earlyFourClocks A))) := by
    rw [bulkClocks,e,Finset.image_insert,Finset.image_insert,Finset.image_insert,firstFourOffRows_image]
  exact ⟨one,one.trans (Finset.insert_comm _ _ _)⟩

private theorem cofactor_insert_three (S : Finset K) {a d e : K}
    (na : a∉S) (nd : d∉S) (ne : e∉S) (ad : a≠d) (ae : a≠e) (de : d≠e) :
    (nodalHull ((insert a (insert d (insert e S))).erase a)).eval a
      =(nodalHull S).eval a*(a-d)*(a-e) := by
  have nc : a∉insert d (insert e S) := by simp [na,ad,ae]
  rw [Finset.erase_insert nc]
  unfold nodalHull
  rw [Finset.prod_insert (by simp [nd,de]),Finset.prod_insert ne]
  simp only [eval_mul,eval_sub,eval_X,eval_C]
  ring

theorem five_tail_cofactor_products
    (five : (offKnots A).card=5) (cleanFive : (cleanKnots A).card=5)
    {theta : K} (H : ExceptionalHead A theta) {x z : Fin 10} (T : FiveCleanTail A x z) :
    bulkCofactor A (nodes A 7)=(earlyFourHull A).eval (nodes A 7)*
      (nodes A 7-nodes A 6)*(nodes A 7-nodes A 8) ∧
    bulkCofactor A (nodes A 8)=(earlyFourHull A).eval (nodes A 8)*
      (nodes A 8-nodes A 6)*(nodes A 8-nodes A 7) := by
  have inj := bulk_clock_inj five cleanFive H T
  have disj : Disjoint firstFourOffRows lastThreeRows := by decide
  have subset : firstFourOffRows⊆bulkRows := by decide
  have eN (j : Fin 10) (hj : j∈lastThreeRows) : nodes A j∉earlyFourClocks A := by
    intro h
    rw [←firstFourOffRows_image] at h
    obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp h
    have e := inj (subset hi) (lateRows_bulk hj) eq
    exact Finset.disjoint_left.mp disj hi (e.symm ▸ hj)
  have e6 := eN 6 (by decide)
  have e7 := eN 7 (by decide)
  have e8 := eN 8 (by decide)
  have b6 : (6:Fin 10)∈bulkRows := by decide
  have b7 : (7:Fin 10)∈bulkRows := by decide
  have b8 : (8:Fin 10)∈bulkRows := by decide
  have n67 : nodes A 6≠nodes A 7 := fun e=>(by decide : (6:Fin 10)≠7) (inj b6 b7 e)
  have n68 : nodes A 6≠nodes A 8 := fun e=>(by decide : (6:Fin 10)≠8) (inj b6 b8 e)
  have n78 : nodes A 7≠nodes A 8 := fun e=>(by decide : (7:Fin 10)≠8) (inj b7 b8 e)
  obtain ⟨one,two⟩ := bulkClock_insertions A
  constructor
  · unfold bulkCofactor
    rw [one,cofactor_insert_three _ e7 e8 e6 n78 n67.symm n68.symm]
    unfold earlyFourHull
    ring
  · unfold bulkCofactor
    rw [two,cofactor_insert_three _ e8 e7 e6 n78.symm n68.symm n67.symm]
    unfold earlyFourHull
    ring

theorem five_tail_early_eval {x z : Fin 10} (T : FiveCleanTail A x z)
    {beta : K} {V : K[X]}
    (rem : earlyFourHull A=C beta*(C 6+C 2*X)+exceptionalQuadratic*V) :
    (earlyFourHull A).eval (nodes A x)=beta*(6+2*nodes A x) ∧
    (earlyFourHull A).eval (nodes A z)=beta*(6+2*nodes A z) := by
  constructor
  · rw [rem]
    simp only [eval_add,eval_mul,eval_C,eval_X,T.qx,zero_mul,add_zero]
  · rw [rem]
    simp only [eval_add,eval_mul,eval_C,eval_X,T.qz,zero_mul,add_zero]

theorem five_off_tail_at_six_impossible
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (five : (offKnots A).card=5) (cleanFive : (cleanKnots A).card=5)
    {theta : K} (H : ExceptionalHead A theta) (S : CenterPrefix A 4)
    (T : FiveCleanTail A 6 8) (g5 : g A 5≠0)
    {beta : K} (bn : beta≠0) {V : K[X]}
    (rem : earlyFourHull A=C beta*(C 6+C 2*X)+exceptionalQuadratic*V) : False := by
  have g7 : g A 7≠0 := by
    intro g
    rcases (T.clean_iff 7).mp g with h|h|h
    · exact (by decide : (7:Fin 10)∉anchorRows) h
    · exact (by decide : (7:Fin 10)≠6) h
    · exact (by decide : (7:Fin 10)≠8) h
  have b7 := five_off_weights_are_zero ha ho five H 7 g7
  have b8 := (clean_quadratic_weights_equal_nonzero ha ho p five H S T).2
  obtain ⟨sigma,e⟩ := five_tail_reflection_rows ha ho p five cleanFive H S T g5
  have e1 := e 1 (by decide) (by decide)
  have e2 := e 2 (by decide) (by decide)
  norm_num only [Nat.reduceAdd,Nat.cast_ofNat,pow_one] at e1 e2
  rw [b7] at e1 e2
  let Xc := nodes A 6
  let Zc := nodes A 8
  let NX := (earlyFourHull A).eval Xc
  let NZ := (earlyFourHull A).eval Zc
  let M2 := Zc^2*NX+Xc^2*NZ
  let M3 := Zc^3*NX+Xc^3*NZ
  change 2*sigma*(0*(1-nodes A 7)*bulkCofactor A (nodes A 7)-b 8*Xc*bulkCofactor A Zc)=b 8*M2 at e1
  change 3*sigma*(0*(1-nodes A 7)^2*bulkCofactor A (nodes A 7)-b 8*Xc^2*bulkCofactor A Zc)=b 8*M3 at e2
  have hx : 3*Xc*M2-2*M3=0 := by
    have zz : b 8*(3*Xc*M2-2*M3)=0 := by linear_combination -3*Xc*e1+2*e2
    exact (mul_eq_zero.mp zz).resolve_left b8
  obtain ⟨NXe,NZe⟩ := five_tail_early_eval T rem
  change NX=beta*(6+2*Xc) at NXe
  change NZ=beta*(6+2*Zc) at NZe
  have v : beta*((6+2*Zc)*Xc^3+(6+2*Xc)*Zc^2*(3*Xc-2*Zc))=0 := by
    dsimp only [M2,M3] at hx
    rw [NXe,NZe] at hx
    linear_combination hx
  exact impossible_four_late p T.sum_one T.prod_eight ((mul_eq_zero.mp v).resolve_left bn)

theorem five_off_tail_at_seven_impossible
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (five : (offKnots A).card=5) (cleanFive : (cleanKnots A).card=5)
    {theta : K} (H : ExceptionalHead A theta) (S : CenterPrefix A 4)
    (T : FiveCleanTail A 7 8) (g5 : g A 5≠0) (clock5 : nodes A 5=2)
    {beta : K} (bn : beta≠0) {V : K[X]}
    (rem : earlyFourHull A=C beta*(C 6+C 2*X)+exceptionalQuadratic*V) : False := by
  obtain ⟨bEq,b8⟩ := clean_quadratic_weights_equal_nonzero ha ho p five H S T
  obtain ⟨sigma,e⟩ := five_tail_reflection_rows ha ho p five cleanFive H S T g5
  have e1 := e 1 (by decide) (by decide)
  have e2 := e 2 (by decide) (by decide)
  norm_num only [Nat.reduceAdd,Nat.cast_ofNat,pow_one] at e1 e2
  have y7 : 1-nodes A 7=nodes A 8 := by linear_combination -T.sum_one
  rw [bEq,y7] at e1 e2
  let Xc := nodes A 7
  let Zc := nodes A 8
  let Fc := nodes A 6
  let NX := (earlyFourHull A).eval Xc
  let NZ := (earlyFourHull A).eval Zc
  let CX := bulkCofactor A Xc
  let CZ := bulkCofactor A Zc
  let M2 := Zc^2*NX+Xc^2*NZ
  let M3 := Zc^3*NX+Xc^3*NZ
  let A1 := Zc*CX-Xc*CZ
  let A2 := Zc^2*CX-Xc^2*CZ
  change 2*sigma*(b 8*Zc*CX-b 8*Xc*CZ)=b 8*M2 at e1
  change 3*sigma*(b 8*Zc^2*CX-b 8*Xc^2*CZ)=b 8*M3 at e2
  have row1 : 2*sigma*A1=M2 := mul_left_cancel₀ b8 (by dsimp only [A1]; linear_combination e1)
  have row2 : 3*sigma*A2=M3 := mul_left_cancel₀ b8 (by dsimp only [A2]; linear_combination e2)
  have test : 3*A2*M2-2*A1*M3=0 := by linear_combination -3*A2*row1+2*A1*row2
  obtain ⟨CXe,CZe⟩ := five_tail_cofactor_products five cleanFive H T
  change CX=NX*(Xc-Fc)*(Xc-Zc) at CXe
  change CZ=NZ*(Zc-Fc)*(Zc-Xc) at CZe
  obtain ⟨NXe,NZe⟩ := five_tail_early_eval T rem
  change NX=beta*(6+2*Xc) at NXe
  change NZ=beta*(6+2*Zc) at NZe
  let D_X := 6+2*Xc
  let D_Z := 6+2*Zc
  let U := D_X*Zc^2
  let V' := D_Z*Xc^2
  have scaled : beta*beta*(Xc-Zc)*
      (3*(U*(Xc-Fc)+V'*(Zc-Fc))*(U+V')
       -2*(D_X*Zc*(Xc-Fc)+D_Z*Xc*(Zc-Fc))*(U*Zc+V'*Xc))=0 := by
    dsimp only [A1,A2,M2,M3] at test
    rw [CXe,CZe,NXe,NZe] at test
    dsimp only [U,V',D_X,D_Z]
    linear_combination test
  have fn : nodes A 6=2 := by
    apply fifth_off_eq_two p T.sum_one T.prod_eight
    exact (mul_eq_zero.mp scaled).resolve_left
      (mul_ne_zero (mul_ne_zero bn bn) (sub_ne_zero.mpr T.clocks_ne))
  have g6 : g A 6≠0 := by
    intro g
    rcases (T.clean_iff 6).mp g with h|h|h
    · exact (by decide : (6:Fin 10)∉anchorRows) h
    · exact (by decide : (6:Fin 10)≠7) h
    · exact (by decide : (6:Fin 10)≠8) h
  have inj := (order8_tag_injective_of_full_count (A:=A) (by omega)).2
  exact (by decide : (6:Fin 10)≠5) (inj _ _ g6 g5 (fn.trans clock5.symm))

end RKResearch.Certified.Graded.ERK8CharEleven.FiveOff

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.FiveOff.five_off_tail_at_six_impossible
#print axioms RKResearch.Certified.Graded.ERK8CharEleven.FiveOff.five_off_tail_at_seven_impossible
