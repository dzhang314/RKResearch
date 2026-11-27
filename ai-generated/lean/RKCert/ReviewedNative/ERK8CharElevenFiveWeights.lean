module

public import RKCert.ReviewedNative.ERK8CharElevenFiveGeometry

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! The two actual quadratic clean weights are equal and nonzero.
Only the pure paid quadrature of the anchor hull and its first
monomial multiple are needed. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven.FiveOff

open RKResearch Polynomial OneOff ERKTaggedHorizon ERK8PaidField LobattoEight RKCert.Endpoint
open RKResearch.Certified.Graded.ERK8CharEleven
open scoped Classical Matrix BigOperators

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

theorem sum_pair_of_support {x z : Fin 10} (ne : x≠z) (F : Fin 10→K)
    (h : ∀ j, j≠x → j≠z → F j=0) : (∑ j,F j)=F x+F z := by
  have s : (∑ j∈({x,z}:Finset (Fin 10)),F j)=∑ j,F j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ out
    exact h j (fun e=>out (by simp [e])) (fun e=>out (by simp [e]))
  rw [←s,Finset.sum_pair ne]

theorem five_off_weights_are_zero
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b)
    (five : (offKnots A).card=5) {theta : K} (H : ExceptionalHead A theta)
    (j : Fin 10) (gj : g A j≠0) : b j=0 := by
  apply five_off_actual_weights_zero ha ho five (P:=C theta*exceptionalQuadratic) _ j gj
  intro i gi
  simpa only [eval_mul,eval_C] using H.fit i gi

theorem paid_X_anchor_probe_one (ho : HasOrder 8 A b) (p : (11:K)=0) :
    probe A b 0 (evalNodes A (X*highAnchorHull))=1 := by
  have d : ((X:K[X])*highAnchorHull).natDegree≤4 :=
    natDegree_mul_le_of_le (show (X:K[X]).natDegree≤1 by simp) highAnchorHull_degree
  have e := probe_evalNodes ho ((X:K[X])*highAnchorHull) 0 (by omega)
  rw [pow_zero,one_mul] at e
  have pol : (X:K[X])*highAnchorHull=monomial 2 6+monomial 3 (-7)+monomial 4 1 := by
    simp only [highAnchorHull,←C_mul_X_pow_eq_monomial,map_neg,map_ofNat,map_one,one_mul]
    ring
  have prim : (primitive ((X:K[X])*highAnchorHull)).eval 1=(6:K)/3+(-7)/4+1/5 := by
    rw [pol]
    simp only [map_add,primitive_monomial,eval_add,eval_monomial,one_pow,mul_one,Nat.reduceAdd,Nat.cast_ofNat]
  rw [prim] at e
  have n3 : (3:K)≠0 := (ho.natCast_isUnit (n:=3) (by decide) (by decide)).ne_zero
  have n4 : (4:K)≠0 := (ho.natCast_isUnit (n:=4) (by decide) (by decide)).ne_zero
  have n5 : (5:K)≠0 := (ho.natCast_isUnit (n:=5) (by decide) (by decide)).ne_zero
  have v3 := div_mul_cancel₀ (6:K) n3
  have v4 := div_mul_cancel₀ (-7:K) n4
  have v5 := div_mul_cancel₀ (1:K) n5
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero n3 n4) n5)
  linear_combination 60*e+20*v3+15*v4+12*v5-3*p

theorem quadrature_through_two_clean
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b)
    (five : (offKnots A).card=5)
    {theta : K} (H : ExceptionalHead A theta) (S : CenterPrefix A 4)
    {x z : Fin 10} (T : FiveCleanTail A x z)
    (P : K[X]) (van : ∀ c∈({0,1,6}:Finset K),P.eval c=0) :
    probe A b 0 (evalNodes A P)=b x*P.eval (nodes A x)+b z*P.eval (nodes A z) := by
  simp only [probe,row_apply,dotProduct,pow_zero,mul_one,evalNodes_apply]
  apply sum_pair_of_support (ne_of_lt T.xz)
  intro i ix iz
  by_cases gi : g A i=0
  · rcases (T.clean_iff i).mp gi with m|e|e
    · rw [van _ (anchor_clock_mem H S m),mul_zero]
    · exact (ix e).elim
    · exact (iz e).elim
  · rw [five_off_weights_are_zero ha ho five H i gi,zero_mul]

theorem clean_quadratic_weights_equal_nonzero
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (five : (offKnots A).card=5)
    {theta : K} (H : ExceptionalHead A theta) (S : CenterPrefix A 4)
    {x z : Fin 10} (T : FiveCleanTail A x z) :
    b x=b z ∧ b z≠0 := by
  let Xc := nodes A x
  let Zc := nodes A z
  let P : K[X] := highAnchorHull
  have zAnti : P.eval Zc=-P.eval Xc := by
    have eq : Zc=1-Xc := by linear_combination T.sum_one
    simp only [P,highAnchorHull,eval_mul,eval_sub,eval_X,eval_C,eq]
    linear_combination Xc*(1-Xc)*p
  have Xnp : Xc∉({0,1,6}:Finset K) :=
    fun h=>exceptional_quadratic_ne_at_anchors ho p h T.qx
  have n0 : Xc≠0 := fun h=>Xnp (by simp [h])
  have n1 : Xc≠1 := fun h=>Xnp (by simp [h])
  have n6 : Xc≠6 := fun h=>Xnp (by simp [h])
  have Xne : P.eval Xc≠0 := by
    simp only [P,highAnchorHull,eval_mul,eval_sub,eval_X,eval_C]
    exact mul_ne_zero (mul_ne_zero n0 (sub_ne_zero.mpr n6)) (sub_ne_zero.mpr n1)
  have q0 := quadrature_through_two_clean ha ho five H S T P (fun c hc=>highAnchorHull_zero hc)
  change probe A b 0 (evalNodes A highAnchorHull)=b x*P.eval Xc+b z*P.eval Zc at q0
  rw [paid_anchor_probe_zero ho p,zAnti] at q0
  have jp : (b x-b z)*P.eval Xc=0 := by linear_combination -q0
  have eq := sub_eq_zero.mp ((mul_eq_zero.mp jp).resolve_right Xne)
  refine ⟨eq,?_⟩
  intro bz
  have qp := quadrature_through_two_clean ha ho five H S T (X*P) (fun c hc=>by
    rw [eval_mul,show P.eval c=0 from highAnchorHull_zero hc,mul_zero])
  change probe A b 0 (evalNodes A (X*highAnchorHull))=
    b x*(X*P).eval Xc+b z*(X*P).eval Zc at qp
  rw [paid_X_anchor_probe_one ho p,eq,bz,zero_mul,zero_mul,add_zero] at qp
  exact one_ne_zero qp

end RKResearch.Certified.Graded.ERK8CharEleven.FiveOff

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.FiveOff.clean_quadratic_weights_equal_nonzero
