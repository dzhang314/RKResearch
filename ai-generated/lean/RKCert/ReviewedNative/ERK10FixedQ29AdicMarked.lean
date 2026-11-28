module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicCardinalReadout

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical

open PaidBarycentric Nonlinear Polynomial
open scoped Ring BigOperators Polynomial

noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

variable {R : Type*} [CommRing R]

def ordInv (x : Site → R) (i : Site) : R := (Den ordinary x i)⁻¹ʳ
def etaNoncenter (U : Polynomial R) (x : Site → R) (i : Site) : R :=
  -(U.eval (x i))
def uAggregate (x : Site → R) (scale : R) (i : Site) : R := scale*ordInv x i

def splitLambda (U : Polynomial R) (x : Site → R) (scale : R) : R :=
  -(∑ i∈withoutCenter, etaNoncenter U x i*uAggregate x scale i)

def normQuad (c : R) : Polynomial R := (X-C 15)*actualQ1 c
def normMass (c : R) (x : Site → R) (i : Site) : R :=
  (normQuad c).eval (x i)*ordInv x i

theorem split_sites : ∀ i : Site, i∈withoutCenter →
    (i∈ordinary ∧ i≠center ∧
      ordinary.erase i=insert center (withoutCenter.erase i) ∧
      center∉withoutCenter.erase i) := by decide +kernel

theorem singleton_flags : ∀ i : Site, i∈singletonSites →
    i≠endNode ∧ i≠oldOrigin ∧ i≠center ∧ i≠host ∧
      i∈cardSites ∧ i∈ordinary ∧ i∈withoutCenter := by decide +kernel

theorem ordinary_extras : ∀ i : Site, i∈singletonSites →
    ordinary.erase i=insert host (insert center (singletonSites.erase i)) ∧
      host∉insert center (singletonSites.erase i) := by decide +kernel

theorem den_card_single (c a b : R) {i : Site} (hi : i∈singletonSites) :
    Den cardSites (nodal c a b) i =
      (nodal c a b i*(nodal c a b i-1))*
      ((nodal c a b i-c)*Den singletonSites (nodal c a b) i) := by
  obtain ⟨hc,ho,hz⟩ := three_card_exclusions i
  unfold Den
  rw [erase_card_sites i hi,Finset.prod_insert hz,Finset.prod_insert ho,Finset.prod_insert hc]
  have h0 : nodal c a b endNode=0 := rfl
  have h1 : nodal c a b oldOrigin=1 := rfl
  have h2 : nodal c a b center=c := rfl
  rw [h0,h1,h2,sub_zero]
  ring

theorem den_ord_single (c a b : R) {i : Site} (hi : i∈singletonSites) :
    Den ordinary (nodal c a b) i = (nodal c a b i-15)*
      ((nodal c a b i-c)*Den singletonSites (nodal c a b) i) := by
  obtain ⟨he,hh⟩ := ordinary_extras i hi
  have hcc := (three_card_exclusions i).1
  unfold Den
  rw [he,Finset.prod_insert hh,Finset.prod_insert hcc]
  rfl

theorem center_times_inverse {x : Site→R} (paid : Paid ordinary x)
    {i : Site} (hi : i∈withoutCenter) :
    (x i-x center)*ordInv x i = (Den withoutCenter x i)⁻¹ʳ := by
  obtain ⟨hord,_,he,hc⟩ := split_sites i hi
  have h9 := den_unit paid hord
  have h8 : IsUnit (Den withoutCenter x i) := by
    apply den_unit _ hi
    intro j hj l hl hne
    exact paid j (split_sites j hj).1 l (split_sites l hl).1 hne
  have hs : Den ordinary x i = (x i-x center)*Den withoutCenter x i := by
    unfold Den
    rw [he,Finset.prod_insert hc]
  apply h8.mul_left_cancel
  calc
    _ = Den ordinary x i*ordInv x i := by rw [hs];ring
    _ = 1 := Ring.mul_inverse_cancel _ h9
    _ = _ := (Ring.mul_inverse_cancel _ h8).symm

theorem natDegreeNormQuad (c : R) : (normQuad c).natDegree≤2 := by
  have hX : (X-C (15:R)).natDegree≤1 :=
    (natDegree_sub_le ..).trans (max_le natDegree_X_le (by simp))
  have hq : (actualQ1 c).natDegree≤1 := natDegree_fromCoeffs _
  exact (natDegree_mul_le ..).trans (Nat.add_le_add hX hq)

/-- All six weighted clock marks, before splitting the single pooled center. -/
theorem weighted_mark_norm [Nontrivial R] {x : Site→R} (pay : Paid ordinary x)
    (c : R) (j : ℕ) (hj : j≤5) :
    ∑ i∈ordinary, (x i)^j*normMass c x i=0 := by
  have hdeg : ((X^j)*normQuad c).natDegree<ordinary.card-1 := by
    rw [ordinary_card]
    exact (natDegree_mul_le ..).trans_lt (by
      have H := natDegree_X_pow_le (R:=R) j
      have D := natDegreeNormQuad c
      omega)
  have h := low_sum pay ((X^j)*normQuad c) hdeg
  simpa only [eval_mul,eval_pow,eval_X,normMass,ordInv,mul_assoc] using h

theorem lifted_low_sum [Nontrivial R] {x : Site→R} (pay : Paid ordinary x)
    (U : Polynomial R) (scale : R) {q : Polynomial R}
    (hU : U.natDegree≤4) (hq : q.natDegree≤2) :
    ∑ i∈withoutCenter,
      (x i-x center)*q.eval (x i)*(etaNoncenter U x i*uAggregate x scale i)=0 := by
  have pay8 : Paid withoutCenter x := by
    intro i hi j hj hij
    exact pay i (split_sites i hi).1 j (split_sites j hj).1 hij
  have hdeg : (C (-scale)*(U*q)).natDegree<withoutCenter.card-1 := by
    rw [withoutCenter_card]
    exact (natDegree_C_mul_le ..).trans_lt ((natDegree_mul_le ..).trans_lt (by omega))
  have h := low_sum pay8 (C (-scale)*(U*q)) hdeg
  rw [←h]
  apply Finset.sum_congr rfl
  intro i hi
  rw [eval_mul,eval_C,eval_mul,←center_times_inverse pay hi]
  unfold etaNoncenter uAggregate
  ring

/-- The three actual eliminated center moments, with arbitrary cofactor scale. -/
theorem eliminated_marks [Nontrivial R] {x : Site→R} (pay : Paid ordinary x)
    (U : Polynomial R) (scale : R) (hU : U.natDegree≤4) (j : ℕ) (hj : j≤2) :
    ∑ i∈withoutCenter,
      (x i-x center)*(x i)^j*(etaNoncenter U x i*uAggregate x scale i)=0 := by
  have h := lifted_low_sum pay U scale (q:=X^j) hU ((natDegree_X_pow_le j).trans hj)
  simpa only [eval_pow,eval_X] using h

/-- One pooled center value makes all four low mixed marks zero, as
required before choosing the two physical center scores. -/
theorem completed_u_marks [Nontrivial R] {x : Site→R} (pay : Paid ordinary x)
    (U : Polynomial R) (scale : R) (hU : U.natDegree≤4) (j : ℕ) (hj : j≤3) :
    (∑ i∈withoutCenter, (x i)^j*(etaNoncenter U x i*uAggregate x scale i))+
      (x center)^j*splitLambda U x scale=0 := by
  have hv : IsRoot (X^j-C ((x center)^j) : Polynomial R) (x center) := by
    simp [IsRoot]
  obtain ⟨q,hq⟩ := dvd_iff_isRoot.mpr hv
  have hdeg : q.natDegree≤2 := by
    by_cases hq0 : q=0
    · simp [hq0]
    · have hL : (X^j-C ((x center)^j) : Polynomial R).natDegree≤j :=
        (natDegree_sub_le ..).trans (max_le (natDegree_X_pow_le j) ((natDegree_C _).le.trans (Nat.zero_le _)))
      rw [hq,(monic_X_sub_C _).natDegree_mul' hq0,natDegree_X_sub_C] at hL
      omega
  have z := lifted_low_sum pay U scale hU hdeg
  rw [splitLambda,mul_neg,←sub_eq_add_neg,Finset.mul_sum,←Finset.sum_sub_distrib,←z]
  apply Finset.sum_congr rfl
  intro i _
  have hread := congrArg (fun p : Polynomial R => p.eval (x i)) hq
  simp only [eval_sub,eval_X,eval_C,eval_mul,eval_pow] at hread
  rw [←hread]
  ring

section Actual
variable (ρ : R →+* F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
variable (haRoot : (headQuadratic c).eval a=0) (hbEq : b=headSum c-a)
include ρ hp hc ha hb haRoot hbEq

/-- At each ordinary noncenter site the actual score times the actual
dirt read from the quartic is the required normalized cofactor contact. -/
theorem actual_noncenter_contact {i : Site} (hi : i∈withoutCenter) :
    score (nodal c a b) i*etaNoncenter (closureU c) (nodal c a b) i =
      normMass c (nodal c a b) i := by
  let x := nodal c a b
  by_cases hh : i=host
  · subst i
    have hR : nodal c a b host=15 := rfl
    simp [score,normMass,normQuad,hR]
  have hs : i∈singletonSites := Finset.mem_erase.mpr ⟨hh,hi⟩
  obtain ⟨h0,h1,_,_,hcard,hord,_⟩ := singleton_flags i hs
  have pC := actual_paid_sites ρ c a b hc ha hb cardSites
  have pO := actual_paid_sites ρ c a b hc ha hb ordinary
  have pAll := actual_paid_sites ρ c a b hc ha hb Finset.univ
  have hD := den_unit pC hcard
  have hD9 := den_unit pO hord
  have hz0 := pAll i (Finset.mem_univ _) endNode (Finset.mem_univ _) h0
  have hz1 := pAll i (Finset.mem_univ _) oldOrigin (Finset.mem_univ _) h1
  have hu : IsUnit (x i*(x i-1)) := by
    have hu0 : IsUnit (x i) := by simpa only [show nodal c a b endNode=0 by rfl,sub_zero] using hz0
    have hu1 : IsUnit (x i-1) := by simpa only [show nodal c a b oldOrigin=1 by rfl] using hz1
    exact hu0.mul hu1
  have hCard : Den cardSites x i*score x i = (actualMu c).eval (x i) := by
    rw [score,ite_eq_right hh,den_mul_cardinal hD,true_cardinal_numerator haRoot hbEq hs]
  have hDiv := (modByMonic_eq_zero_iff_dvd (monicD7 c)).mp (closure_remainder_zero ρ c hp hc)
  have hzr : (actualD7 c).eval (x i)=0 := by
    rw [actualD7_roots haRoot hbEq]
    exact rootPoly_eval_zero _ hs
  have hEval := eval_eq_zero_of_dvd_of_eval_eq_zero hDiv hzr
  simp only [eval_sub,eval_mul,eval_X,eval_one] at hEval
  have hE : (actualMu c).eval (x i)*etaNoncenter (closureU c) x i =
      (x i*(x i-1))*(actualQ1 c).eval (x i) := by
    rw [etaNoncenter,mul_neg,sub_eq_zero.mp hEval]
    ring
  have hLive :
      ((x i-c)*Den singletonSites x i)*(score x i*etaNoncenter (closureU c) x i) =
        (actualQ1 c).eval (x i) := by
    apply hu.mul_left_cancel
    calc
      _ = (Den cardSites x i*score x i)*etaNoncenter (closureU c) x i := by
        rw [den_card_single c a b hs]; ring
      _ = _ := by rw [hCard,hE]
  change score x i*etaNoncenter (closureU c) x i = normMass c x i
  apply hD9.mul_left_cancel
  calc
    _ = (x i-15)*(((x i-c)*Den singletonSites x i)*
                 (score x i*etaNoncenter (closureU c) x i)) := by
      rw [den_ord_single c a b hs]; ring
    _ = (normQuad c).eval (x i) := by rw [hLive]; simp [normQuad]
    _ = _ := by unfold normMass ordInv; rw [mul_left_comm,Ring.mul_inverse_cancel _ hD9,mul_one]

end Actual
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.weighted_mark_norm
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.eliminated_marks
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.completed_u_marks
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_noncenter_contact
