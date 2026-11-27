module

public import RKCert.ReviewedNative.ERK8CharElevenTailMoments

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Closing the literal seven-off branch from the early chart
The only nonliteral inputs are the chronological late-three window,
the early hull modulo the exceptional quadratic, and membership of
the early off clock 2. Every reverse and normalization condition is
earned from the reviewed order-eight predicate. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven

open RKResearch Polynomial OneOff ERKTaggedHorizon ERK8PaidField LobattoEight RKCert.Endpoint
open scoped Matrix Classical BigOperators

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

/-- The already-earned product of the last two off clocks and the
last-three hull remainder force the first tail clock to be 2. -/
theorem high_fifth_clock_of_hull
    (p : (11:K)=0)
    (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3)
    {f u v : Fin 10} (T : HighPhysicalTail A f u v)
    {theta : K} (H : ExceptionalHead A theta)
    (uv_product : nodes A u*nodes A v=8) {delta : K} {Z : K[X]}
    (hF : highTailHull A f u v=C delta*(1+C 7*X)+exceptionalQuadratic*Z) :
    nodes A f=2 := by
  let F := highTailHull A f u v
  let t := nodes A f
  let x := nodes A u
  let z := nodes A v
  let s := 1-(x+z)
  let q : K[X] := exceptionalQuadratic
  let R : K[X] := C s*(C (1-t)*X-C 8)
  let L : K[X] := C delta*(1+C 7*X)
  obtain ⟨fx,fz,xz⟩ := highTailClocks_distinct seven three T
  have hProd : F=(X-C t)*(X-C x)*(X-C z) := by
    change nodalHull (highTailClocks A f u v)=_
    unfold nodalHull highTailClocks
    rw [Finset.prod_insert (by simp [fx,fz]),Finset.prod_pair xz]
    dsimp only [t,x,z]
    ring
  have P2 : (X-C x)*(X-C z)=q+C s*X := by
    have e := congrArg (C : K→+*K[X]) uv_product
    rw [map_mul] at e
    dsimp only [q,exceptionalQuadratic,s]
    simp only [map_sub,map_add,map_one]
    linear_combination e
  have hProj : F=q*(X-C t+C s)+R := by
    calc
      F=(X-C t)*((X-C x)*(X-C z)) := by rw [hProd]; ring
      _ = _ := by
        rw [P2]
        dsimp only [R,q,exceptionalQuadratic]
        simp only [map_sub,map_one]
        ring
  change F=L+q*Z at hF
  have dCX : (C (1-t)*X).natDegree≤1 := (natDegree_C_mul_le _ _).trans (by simp)
  have dC8 : (C (8:K)).natDegree≤1 := by simp
  have dR : R.natDegree≤1 :=
    (natDegree_C_mul_le _ _).trans (natDegree_sub_le_of_le dCX dC8)
  have dL : L.natDegree≤1 := by
    apply (natDegree_C_mul_le _ _).trans
    simpa only [map_one] using affine_degree_le (1:K) 7
  have dv : q∣R-L := by
    refine ⟨Z-(X-C t+C s),?_⟩
    linear_combination hF-hProj
  have eq : R=L := sub_eq_zero.mp
    (low_quadratic_multiple_eq_zero (natDegree_sub_le_of_le dR dL) dv)
  have e0 := congrArg (fun P : K[X] => P.coeff 0) eq
  have e1 := congrArg (fun P : K[X] => P.coeff 1) eq
  have qx : x^2-x+8≠0 := by
    simpa only [x,exceptionalQuadratic_eval] using exceptional_quadratic_ne_off H T.u_off
  have c0 : -8*(1-(x+z))=delta := by
    simp [R,L,s,coeff_C,coeff_X] at e0
    linear_combination e0
  have c1 : (1-(x+z))*(1-t)=7*delta := by
    have c8 : (C (8:K)).coeff 1=0 := by simp
    have cOne : (1:K[X]).coeff 1=0 := by simp [coeff_one]
    simp only [R,L,coeff_C_mul,coeff_sub,coeff_add,coeff_X_one,c8,cOne,mul_one,sub_zero,zero_add] at e1
    dsimp only [s] at e1
    linear_combination e1
  exact high_fifth_eq_two p qx uv_product c0 c1

/-- Native conditional exclusion. The required early chart consists
precisely of its physical last-three indices, the early hull residue,
and clock 2 in that early hull. No scalar moment ratio is assumed. -/
theorem seven_off_contradiction_of_early_chart
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3)
    {f u v : Fin 10} (T : HighPhysicalTail A f u v)
    (early : ∃ beta : K, beta≠0 ∧ ∃ V : K[X],
      highPrefixHull A f u v=C beta*(C 6+C 2*X)+exceptionalQuadratic*V)
    (twoEarly : (2:K) ∈ offKnots A \ highTailClocks A f u v) : False := by
  obtain ⟨theta,H⟩ := order8_paid_five_or_seven_exceptional_head ha ho p (Or.inr ⟨seven,three⟩)
  obtain ⟨delta,dn,Z,hull⟩ := seven_off_paid_tail_hull_remainder ha ho p seven three T early
  obtain ⟨mn,ratio⟩ := highTail_moments_of_hull_remainder p seven three T H dn hull
  have product := seven_off_paid_tail_product_of_ratio ha ho p seven three T mn ratio
  have f2 := high_fifth_clock_of_hull p seven three T H product hull
  exact (Finset.mem_sdiff.mp twoEarly).2 (by simp [highTailClocks,f2])

end RKResearch.Certified.Graded.ERK8CharEleven

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.high_fifth_clock_of_hull
#print axioms RKResearch.Certified.Graded.ERK8CharEleven.seven_off_contradiction_of_early_chart
