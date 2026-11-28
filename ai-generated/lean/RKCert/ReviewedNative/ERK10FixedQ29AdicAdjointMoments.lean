module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicOrderBush
public import RKCert.ReviewedNative.ERK10FixedQ29AdicAdjointCore

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical

open Nonlinear Polynomial
open scoped Ring BigOperators Polynomial
noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 20000
variable {R : Type*} [CommRing R]

theorem avgRaw_int_as_line (f : ℤ→ℤ) :
    avgRaw f=RKResearch.Certified.ERK10AdjointCore.integralNumerator f := by
  simp only [avgRaw,Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.val_succ,Fin.val_zero,
    avgNumerator,RKResearch.Certified.ERK10AdjointCore.integralNumerator]
  ring

/-- Exact finite formal integration by parts for the affine-reflected
monomials that can appear in a degree-nine raw pairing. -/
theorem beta_integer_grid :
    ∀ k i : Fin 9, k.val+i.val≤8 →
      (((i.val+1:ℕ):ℤ))*avgRaw (fun y : ℤ => y^(k.val+1)*(1-y)^i.val) =
      (((k.val+1:ℕ):ℤ))*avgRaw (fun y : ℤ => y^k.val*(1-y)^(i.val+1)) := by
  intro k i h
  rw [avgRaw_int_as_line,avgRaw_int_as_line]
  exact RKResearch.Certified.ERK10AdjointCore.beta_grid k i h

theorem cast_avg_mixed (k i : ℕ) :
    (Int.castRingHom R) (avgRaw (fun y : ℤ=>y^k*(1-y)^i)) =
      avgRaw (fun y : R=>y^k*(1-y)^i) := by
  simp only [avgRaw,map_sum,map_mul,map_pow,map_sub,map_one]
  apply Finset.sum_congr rfl
  intro j _
  change (avgNumerator j.val:R)*(((j.val:ℤ):R)^k*(1-((j.val:ℤ):R))^i)=_
  rw [Int.cast_natCast]

theorem jacobi_integer_grid :
    ∀ i : Fin 5, i.val≠0 →
      avgRaw (fun y : ℤ=>jacobiJ y*(1-y)^i.val)=0 := by
  intro i h
  rw [avgRaw_int_as_line]
  exact RKResearch.Certified.ERK10AdjointCore.jacobi_grid i h

theorem cast_jacobi_mixed (i : ℕ) :
    (Int.castRingHom R) (avgRaw (fun y : ℤ=>jacobiJ y*(1-y)^i)) =
      avgRaw (fun y : R=>jacobiJ y*(1-y)^i) := by
  simp only [avgRaw,jacobiJ,map_sum,map_mul,map_pow,map_sub,map_one,map_add,map_ofNat]
  apply Finset.sum_congr rfl
  intro j _
  let k := j.val
  change (avgNumerator k:R)*
    ((((k:ℤ):R)-14*((k:ℤ):R)^2+56*((k:ℤ):R)^3-84*((k:ℤ):R)^4+42*((k:ℤ):R)^5)*
      (1-((k:ℤ):R))^i)=_
  rw [Int.cast_natCast]

def actualScoreMixed (c a b : R) (k i : ℕ) : R :=
  ∑ j : Site,rawW c a b j*(rawY c a b j)^k*(rawClock c a b j)^i

def actualCofactorMixed (c a b : R) (k i : ℕ) : R :=
  ∑ j : Site,rawU c a b j*(rawY c a b j)^k*(rawClock c a b j)^i

def actualJacobiMixed (c a b : R) (i : ℕ) : R :=
  ∑ j : Site,rawW c a b j*jacobiJ (rawY c a b j)*(rawClock c a b j)^i

theorem degree_one_minus_X : ((1:Polynomial R)-X).natDegree≤1 :=
  (natDegree_sub_le ..).trans (max_le (by simp) natDegree_X_le)

theorem cofactor_mixed_step (c a b : R) (k i : ℕ) :
    actualCofactorMixed c a b k (i+1) =
      actualCofactorMixed c a b k i-actualCofactorMixed c a b (k+1) i := by
  unfold actualCofactorMixed
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_succ,pow_succ,rawClock]
  ring

section Actual
variable (ρ : R→+*F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
include ρ hp hc ha hb

theorem actual_cofactor_mixed_zero (k i : ℕ) (h : k+i≤7) :
    actualCofactorMixed c a b k i=0 := by
  induction i generalizing k with
  | zero =>
    have H := raw_u_marks ρ c a b hp hc ha hb k (by omega)
    unfold actualCofactorMixed
    simp only [pow_zero,mul_one]
    simpa only [mul_comm] using H
  | succ i ih =>
    rw [cofactor_mixed_step,ih k (by omega),ih (k+1) (by omega),sub_self]

theorem actual_score_mixed (k i : ℕ) (hi : 0 < i) (h : k+i≤9) :
    actualScoreMixed c a b k i=avg (fun y : R=>y^k*(1-y)^i) := by
  let p : Polynomial R := X^k*(1-X)^i
  have hY : (((1:Polynomial R)-X)^i).natDegree ≤ i := by
    simpa only [mul_one] using
      (natDegree_pow_le_of_le i (degree_one_minus_X (R:=R)))
  have hP : p.natDegree≤9 := (natDegree_mul_le ..).trans
    ((Nat.add_le_add (natDegree_X_pow_le k) hY).trans h)
  have H := raw_cardinal ρ c a b hp hc ha hb p hP
  simp only [p,eval_mul,eval_pow,eval_X,eval_sub,eval_one,sub_self,
    zero_pow (Nat.ne_of_gt hi),mul_zero,zero_mul,add_zero,avgLin_apply] at H
  unfold actualScoreMixed rawClock
  calc
    _ = ∑ j : Site,(rawY c a b j)^k*(1-rawY c a b j)^i*rawW c a b j := by
      apply Finset.sum_congr rfl;intro j _;ring
    _ = _ := H

theorem actual_beta_pair (k i : ℕ) (hi : 0 < i) (h : k+i≤8) :
    Ring.inverse (((k+1:ℕ):R))*actualScoreMixed c a b (k+1) i =
      Ring.inverse (((i+1:ℕ):R))*actualScoreMixed c a b k (i+1) := by
  let K : Fin 9 := ⟨k,by omega⟩
  let I : Fin 9 := ⟨i,by omega⟩
  have H := congrArg (Int.castRingHom R) (beta_integer_grid K I (by
    change k+i≤8;exact h))
  simp only [map_mul,cast_avg_mixed] at H
  change (((i+1:ℕ):ℤ):R)*avgRaw (fun y : R=>y^(k+1)*(1-y)^i) =
    (((k+1:ℕ):ℤ):R)*avgRaw (fun y : R=>y^k*(1-y)^(i+1)) at H
  rw [Int.cast_natCast,Int.cast_natCast] at H
  rw [actual_score_mixed ρ c a b hp hc ha hb (k+1) i hi (by omega),
    actual_score_mixed ρ c a b hp hc ha hb k (i+1) (by omega) (by omega)]
  have hK := Ring.mul_inverse_cancel _ (small_order_paid ρ (k+1) (by omega) (by omega))
  have hI := Ring.mul_inverse_cancel _ (small_order_paid ρ (i+1) (by omega) (by omega))
  let U := avgRaw (fun y : R=>y^(k+1)*(1-y)^i)
  let V := avgRaw (fun y : R=>y^k*(1-y)^(i+1))
  let A := Ring.inverse (((k+1:ℕ):R))
  let B := Ring.inverse (((i+1:ℕ):R))
  let D := Ring.inverse (avgDen:R)
  change A*(D*U)=B*(D*V)
  change ((i+1:ℕ):R)*U=((k+1:ℕ):R)*V at H
  change ((k+1:ℕ):R)*A=1 at hK
  change ((i+1:ℕ):R)*B=1 at hI
  linear_combination A*B*D*H-A*D*U*hI+B*D*V*hK

theorem actual_jacobi_mixed_zero (i : ℕ) (hi : 0 < i) (h : i≤4) :
    actualJacobiMixed c a b i=0 := by
  let Jc : Polynomial R := fromCoeffs [0,1,(-14),56,(-84),42]
  have hJ (y : R) : Jc.eval y=jacobiJ y := by
    simp only [Jc,fromCoeffs_eval,RKCert.ReviewedNative.IntegerHornerCertificate.horner,jacobiJ]
    ring
  let p : Polynomial R := Jc*(1-X)^i
  have hL : Jc.natDegree≤5 := natDegree_fromCoeffs _
  have hY : (((1:Polynomial R)-X)^i).natDegree ≤ i := by
    simpa only [mul_one] using
      (natDegree_pow_le_of_le i (degree_one_minus_X (R:=R)))
  have hP : p.natDegree≤9 := (natDegree_mul_le ..).trans
    ((Nat.add_le_add hL hY).trans (by omega))
  have H := raw_cardinal ρ c a b hp hc ha hb p hP
  simp only [p,eval_mul,eval_pow,eval_sub,eval_X,eval_one,hJ,sub_self,
    zero_pow (Nat.ne_of_gt hi),mul_zero,zero_mul,add_zero,avgLin_apply] at H
  let I : Fin 5 := ⟨i,by omega⟩
  have hVal := congrArg (Int.castRingHom R) (jacobi_integer_grid I (by exact Nat.ne_of_gt hi))
  simp only [cast_jacobi_mixed,map_zero] at hVal
  have hR : avgRaw (fun y : R=>jacobiJ y*(1-y)^i)=0 := hVal
  rw [avg,hR,mul_zero] at H
  unfold actualJacobiMixed rawClock
  calc
    _ = ∑ j : Site,jacobiJ (rawY c a b j)*(1-rawY c a b j)^i*rawW c a b j := by
      apply Finset.sum_congr rfl;intro j _;ring
    _ = _ := H

end Actual
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_cofactor_mixed_zero
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_beta_pair
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_jacobi_mixed_zero
