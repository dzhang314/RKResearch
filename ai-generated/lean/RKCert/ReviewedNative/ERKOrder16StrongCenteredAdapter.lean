module

public import RKCert.ReviewedNative.ERKOrder16StrongMaskProducer
public import RKCert.ReviewedNative.ERKOrder16StrongCenteredMoments

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Paid centered moments on the original strong-three contrast rows

Both orientations refer to the same three rows. The reflected cubic
kills the support at the three actual clocks; the maximum spectator
degree is nine. This adapter uses formal reflection only, not
positivity or any scalar exclusion. -/
namespace RKResearch.Certified.ERK16

open RKResearch Module Polynomial
open RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKCert.ReviewedNative.PositiveRule19 RKCert.ReviewedNative.StrongCentered16
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open scoped BigOperators Classical Matrix

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 24) (Fin 24) K} {b w g : Fin 24 → K}
variable {Q P : K[X]}

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem strong_reflect_twice (S : K[X]) :
    (S.comp (1-X)).comp (1-X) = S := by
  rw [comp_assoc]
  have h : ((1-X : K[X]).comp (1-X)) = X := by
    simp only [sub_comp,one_comp,X_comp]
    ring
  rw [h,comp_X]

/-- The actual native (3+2+1) and (2+1) ports, with their
forced origin, pay the scalar chart. The reverse middle test
changes sign under reflection. -/
theorem StrongThreeActualMask.centered_moments
    (M : StrongThreeActualMask A b w g Q P)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 16 A b)
    {ι : Fin 3 → Fin 24} (B : StrongThreePhysicalPorts A b Q P ι)
    (origin : ι 0=0) :
    Moments (Q.comp (1-X)) (nodes A (ι 1)) (nodes A (ι 2)) := by
  let a := nodes A (ι 1)
  let z := nodes A (ι 2)
  let q := Q.comp (1-X)
  have c0 : nodes A (ι 0)=0 := by
    rw [origin]
    change (∑ j,A 0 j*(1 : K))=0
    exact Finset.sum_eq_zero fun j _ => by rw [ha 0 j (Fin.zero_le j),zero_mul]
  have y (i : Fin 24) : reflectedClock A i=1-nodes A i := rfl
  have y_eval (i : Fin 24) : (1-X : K[X]).eval (reflectedClock A i)=nodes A i := by
    rw [eval_sub,eval_one,eval_X,y]
    ring
  have qn : q≠0 := by
    have h := (M.active ((B.rows (ι 0)).mpr ⟨0,rfl⟩)).2.2.2
    have live : q.eval (nodes A (ι 0))≠0 := by
      simpa only [q,eval_comp,eval_sub,eval_one,eval_X,y] using h
    intro hq
    exact live (by rw [hq,eval_zero])
  have qd : q.natDegree≤5 :=
    natDegree_comp_le.trans (by rw [one_sub_X_natDegree,mul_one]; exact M.qDegree)
  have distinct : a≠z := fun e => (by decide : (1 : Fin 3)≠2) (B.simple e)
  have fwd (S : K[X]) (x : K) (h : (primitive S).eval x=0) :
      integral 0 x S=0 := by
    rw [integral_zero_left,formalPrimitive_eq_native]
    exact h
  have rev (S : K[X]) (x : K) (h : (primitive (S.comp (1-X))).eval (1-x)=0) :
      integral x 1 S=0 := by
    rw [←integral_reflect S x,integral_zero_left,formalPrimitive_eq_native]
    exact h
  change Moments q a z
  refine ⟨qn,qd,distinct,?_,?_,?_,?_,?_,?_,?_⟩
  · apply fwd
    simpa only [a,q,c0,C_0,sub_zero,one_mul] using
      B.forwardSecond (1 : K[X]) (by simp)
  · apply fwd
    simpa only [a,q,c0,C_0,sub_zero,pow_two] using
      B.forwardSecond (X : K[X]) (by simp)
  · apply fwd
    simpa only [a,z,q,c0,C_0,sub_zero] using B.forwardThird
  · apply rev
    simpa only [z,q,y,mul_comp,sub_comp,one_comp,X_comp,sub_sub_cancel,
      strong_reflect_twice,one_mul] using B.reverseLast (1 : K[X]) (by simp)
  · apply rev
    simpa only [z,q,y,mul_comp,pow_comp,sub_comp,one_comp,X_comp,sub_sub_cancel,
      strong_reflect_twice,pow_two,mul_assoc] using B.reverseLast (X : K[X]) (by simp)
  · apply rev
    have e : (((1-X)*(X-C z))*q).comp (1-X) = -((X-C (1-z))*(X*Q)) := by
      simp only [q,mul_comp,sub_comp,one_comp,X_comp,C_comp,sub_sub_cancel,
        strong_reflect_twice,map_sub,map_one]
      ring
    rw [e,map_neg,eval_neg,neg_eq_zero]
    simpa only [a,z,y] using B.reverseMiddle
  · intro H hH
    let S : K[X] := X*(X-C a)*(X-C z)*H
    let R := S.comp (1-X)
    have sd : S.natDegree≤9 :=
      natDegree_mul_le_of_le
        (natDegree_mul_le_of_le
          (natDegree_mul_le_of_le natDegree_X.le (natDegree_X_sub_C a).le)
          (natDegree_X_sub_C z).le) hH
    have rd : R.natDegree≤9 :=
      natDegree_comp_le.trans (by rw [one_sub_X_natDegree,mul_one]; exact sd)
    have mass : (∑ i,weightedEval (reflectedClock A) (reverseContrast A b Q P) R i)=0 := by
      refine reverse_contrast_vanishes (A:=A) (reverseContrast A b Q P) R ?_
      intro t ht
      obtain ⟨i,hi,rfl⟩ := mem_weightedSites.mp ht
      have hm : i∈strongThreeRows A b Q P := (Hidden.mem_activeRows i).mpr hi
      obtain ⟨k,rfl⟩ := (B.rows i).mp hm
      change (S.comp (1-X)).eval (reflectedClock A (ι k))=0
      rw [eval_comp,y_eval]
      fin_cases k <;> simp [S,a,z,c0]
    have Qd := M.qDegree
    have Pd := M.pDegree
    have paid := (reverse_contrast_moment ho Q P R (by omega) (by omega)).symm.trans mass
    let T : K[X] := X*(1-X)*((X-C a)*(X-C z)*q)*H
    have e : T.comp (1-X) = R*(X*Q) := by
      simp only [T,R,S,q,mul_comp,sub_comp,one_comp,X_comp,C_comp,sub_sub_cancel,
        strong_reflect_twice]
      ring
    change integral 0 1 T=0
    rw [←integral_reflect T 0,sub_zero,integral_zero_left,formalPrimitive_eq_native,e]
    exact paid

/-- The strong rank-eight frame alone produces the centered scalar
packet. No additional physical exclusion or numerical knot order is
assumed. This statement does not itself exclude the packet. -/
theorem width24_strong_centered_moments
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 16 A b)
    (r7 : finrank K (zeroSpace A 7)=8) :
    ∃ (q : K[X]) (a z : K), Moments q a z := by
  obtain ⟨w,g,Q,P,ι,M,B,origin⟩ := width24_strong_actual_ports_and_origin ha ho r7
  exact ⟨Q.comp (1-X),nodes A (ι 1),nodes A (ι 2),M.centered_moments ha ho B origin⟩

end
end RKResearch.Certified.ERK16
