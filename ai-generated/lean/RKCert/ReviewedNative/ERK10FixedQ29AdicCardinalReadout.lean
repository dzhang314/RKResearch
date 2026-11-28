module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicCardinals

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical

open PaidBarycentric Nonlinear Polynomial
open scoped Ring BigOperators Polynomial

noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

variable {R : Type*} [CommRing R]

def avgLin : Polynomial R →ₗ[R] R where
  toFun p := avg (fun x => p.eval x)
  map_add' p q := by simp only [eval_add,avg,avgRaw_add,mul_add]
  map_smul' r p := by
    simp only [Polynomial.smul_eq_C_mul,eval_mul,eval_C,avg,avgRaw_scale,smul_eq_mul,RingHom.id_apply]
    ring

@[simp] theorem avgLin_apply (p : Polynomial R) : avgLin p = avg (fun x => p.eval x) := rfl

theorem avgLin_C_mul (a : R) (p : Polynomial R) : avgLin (C a*p) = a*avgLin p := by
  simp only [avgLin_apply,eval_mul,eval_C,avg,avgRaw_scale]
  ring

theorem avgLin_basis (s : Finset Site) (x : Site → R) (i : Site) :
    avgLin (basis s x i)=cardinal s x i := by
  rw [basis,avgLin_C_mul,avgLin_apply,cardinal]
  simp_rw [eval_rootPoly]
  exact mul_comm _ _

theorem cardinal_exact [Nontrivial R] {s : Finset Site} {x : Site→R}
    (paid : PaidBarycentric.Paid s x) (p : Polynomial R) (hp : p.natDegree<s.card) :
    ∑ i∈s, p.eval (x i)*cardinal s x i = avgLin p := by
  have hh := congrArg (avgLin : Polynomial R → R) (interp paid p hp)
  simpa only [map_sum,avgLin_C_mul,avgLin_basis] using hh

def p3Poly (c : R) : Polynomial R := X*(X-1)*(X-C c)

/-- The divided difference of the actual monic degree-seven cardinal
denominator, expressed using its real eight coefficients. -/
def ddPoly (c z : R) : Polynomial R := ∑ i : Fin 7,
  C (z^i.val)*(∑ j : Fin 8, if i.val<j.val then C (actualD c j.val)*X^(j.val-1-i.val) else 0)

theorem actualD7_as_sum (c : R) :
    actualD7 c = ∑ j : Fin 8, C (actualD c j.val)*X^j.val := by
  nth_rw 1 [as_sum_range' (actualD7 c) 8 ((natDegreeD7 c).trans_lt (by decide))]
  rw [Finset.sum_range]
  simp only [C_mul_X_pow_eq_monomial,coeff_actualD7]

theorem actualD7_eval_sum (c z : R) :
    (actualD7 c).eval z = ∑ j : Fin 8, actualD c j.val*z^j.val := by
  rw [actualD7_as_sum]
  change (evalRingHom z) _ = _
  rw [map_sum]
  simp

theorem dd_identity (c z : R) :
    (X-C z)*ddPoly c z = actualD7 c-C ((actualD7 c).eval z) := by
  rw [actualD7_eval_sum,actualD7_as_sum,ddPoly]
  norm_num [map_sum,map_mul,map_pow,Fin.sum_univ_succ]
  ring

theorem avgLin_p3_pow (c : R) (i : ℕ) :
    avgLin (p3Poly c*X^i) = actualM c i := by
  simp [avgLin_apply,p3Poly,actualM]

theorem mu_is_divided_average (c z : R) :
    muValue c z = avgLin (p3Poly c*ddPoly c z) := by
  have hc : p3Poly c*ddPoly c z = ∑ i : Fin 7, ∑ j : Fin 8,
      if i.val<j.val then C (z^i.val*actualD c j.val)*(p3Poly c*X^(j.val-1-i.val)) else 0 := by
    rw [ddPoly,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [←mul_assoc,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hj
    · rw [map_mul]
      ring
    · simp
  rw [hc,map_sum]
  unfold muValue muCoeff
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hj
  · rw [avgLin_C_mul,avgLin_p3_pow]
    ring
  · simp only [zero_mul,map_zero]

theorem headQuadratic_split {c a b : R} (ha : (headQuadratic c).eval a=0)
    (hb : b=headSum c-a) :
    headQuadratic c = (X-C a)*(X-C b) := by
  have hs : a+b=headSum c := by rw [hb]; ring
  have hp : a*b=headProduct c := by
    apply sub_eq_zero.mp
    rw [eval_headQuadratic] at ha
    calc
      _ = -(a^2-headSum c*a+headProduct c) := by rw [hb]; ring
      _ = 0 := by rw [ha,neg_zero]
  rw [headQuadratic,←hs,←hp,map_add,map_mul]
  ring

theorem singleton_listing :
    singletonSites = {headA,headB,nodeD,nodeE,nodeF,nodeG,nodeH} := by decide +kernel

theorem actualD7_roots {c a b : R} (ha : (headQuadratic c).eval a=0)
    (hb : b=headSum c-a) : actualD7 c = rootPoly singletonSites (nodal c a b) := by
  rw [actualD7_factor,headQuadratic_split ha hb,singleton_listing,rootPoly]
  simp [Finset.prod_insert, headA,headB,nodeD,nodeE,nodeF,nodeG,nodeH,nodal]
  ac_rfl

theorem dd_at_root {c a b : R} (ha : (headQuadratic c).eval a=0)
    (hb : b=headSum c-a) {i : Site} (hi : i∈singletonSites) :
    ddPoly c (nodal c a b i) = rootPoly (singletonSites.erase i) (nodal c a b) := by
  have hprod := actualD7_roots ha hb
  have hev : (actualD7 c).eval (nodal c a b i)=0 := by
    rw [hprod,rootPoly_eval_zero _ hi]
  have he := dd_identity c (nodal c a b i)
  rw [hev,C_0,sub_zero,hprod,rootPoly_erase _ hi] at he
  exact (monic_X_sub_C _).isRegular.left he

theorem erase_card_sites : ∀ i : Site, i∈singletonSites →
    cardSites.erase i=insert endNode (insert oldOrigin (insert center (singletonSites.erase i))) := by
  decide +kernel

theorem three_card_exclusions : ∀ i : Site,
    center∉(singletonSites.erase i) ∧
    oldOrigin∉insert center (singletonSites.erase i) ∧
    endNode∉insert oldOrigin (insert center (singletonSites.erase i)) := by
  decide +kernel

theorem card_poly_singleton (c a b : R) {i : Site} (hi : i∈singletonSites) :
    rootPoly (cardSites.erase i) (nodal c a b) =
      p3Poly c * rootPoly (singletonSites.erase i) (nodal c a b) := by
  obtain ⟨hc,ho,hz⟩ := three_card_exclusions i
  rw [erase_card_sites i hi,rootPoly_insert _ _ hz,rootPoly_insert _ _ ho,rootPoly_insert _ _ hc]
  simp [p3Poly,nodal,endNode,oldOrigin,center]
  ac_rfl

/-- The checked divided-difference cardinal is the exact numerator of
the true ten-site weight, not merely a residue at that site. -/
theorem true_cardinal_numerator {c a b : R} (ha : (headQuadratic c).eval a=0)
    (hb : b=headSum c-a) {i : Site} (hi : i∈singletonSites) :
    avg (rawNumer cardSites (nodal c a b) i) = (actualMu c).eval (nodal c a b i) := by
  rw [actualMu_eval,mu_is_divided_average,dd_at_root ha hb hi,←card_poly_singleton c a b hi,
    avgLin_apply]
  exact congrArg avg (funext (fun y => (eval_rootPoly _ _ _).symm))

end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.cardinal_exact
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.true_cardinal_numerator
