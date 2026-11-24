module

public import RKCert.PencilOmissionSpecialization


@[expose] public section

/-! # Exact bidegree cap for the symmetric omitted-root divided difference

The two variables may be exchanged before specialization. Structural degree
in the omitted endpoint is therefore certified without a guessed
coefficient fit, a squarefree assumption, or a finite sample. -/
namespace RKCert.FixedPolynomial
open Polynomial
open scoped Classical
noncomputable section

variable {R : Type*} [CommRing R]

/-- Small evaluation adapter for coefficient transposition, built from the
native polynomial ring homomorphisms. The specialization does not need
any bivariate derivative or separability import. -/
def nestedSwap (R : Type*) [CommRing R] : R[X][X]→+*R[X][X] :=
  eval₂RingHom (mapRingHom (C:R→+*R[X])) (C (X:R[X]))

variable (R) in
theorem nestedSwap_Y : nestedSwap R (X:R[X][X])=C (X:R[X]) := by
  simp [nestedSwap]

theorem nestedSwap_C (f : R[X]) : nestedSwap R (C f)=f.map C := by
  simp [nestedSwap]

variable (R) in
theorem nestedSwap_X : nestedSwap R (C (X:R[X]))=X := by
  rw [nestedSwap_C,Polynomial.map_X]

theorem nestedSwap_monomial (n : ℕ) (f : R[X]) :
    nestedSwap R (monomial n f)=f.map C*C (X^n) := by
  rw [←C_mul_X_pow_eq_monomial,map_mul,map_pow,nestedSwap_Y,nestedSwap_C,map_pow]

theorem nestedSwap_monomial_monomial (n m : ℕ) (a : R) :
    nestedSwap R (monomial n (monomial m a))=monomial m (monomial n a) := by
  rw [nestedSwap_monomial,Polynomial.map_monomial]
  calc
    monomial m (C a)*C (X^n) = C (C a)*X^m*C (X^n) := by rw [C_mul_X_pow_eq_monomial]
    _ = C (C a*X^n)*X^m := by rw [map_mul]; ac_rfl
    _ = monomial m (monomial n a) := by simp only [C_mul_X_pow_eq_monomial]

theorem nestedSwap_map_C (f : R[X]) : nestedSwap R (f.map C)=C f := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.map_add,map_add,hp,hq]
  | monomial n a =>
    rw [Polynomial.map_monomial,show (C a:R[X])=monomial 0 a by simp,
      nestedSwap_monomial_monomial]
    simp

theorem swap_coeff_coeff (P : R[X][X]) (i j : ℕ) :
    ((nestedSwap R P).coeff i).coeff j=(P.coeff j).coeff i := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq => simp only [map_add,coeff_add,hp,hq]
  | monomial k a =>
    induction a using Polynomial.induction_on' with
    | add a b ha hb => simp only [map_add,coeff_add,ha,hb]
    | monomial l b =>
      rw [nestedSwap_monomial_monomial]
      by_cases h : l=i <;> by_cases g : k=j <;> simp [coeff_monomial,h,g]

theorem universalOmission_mul (H L : R[X]) :
    (X-C (X:R[X]))*universalOmission H L=C L*H.map C-C H*L.map C := by
  unfold universalOmission
  apply (mul_divByMonic_eq_iff_isRoot).mpr
  change (C L*H.map C-C H*L.map C).eval (X:R[X])=0
  rw [eval_sub,eval_mul,eval_mul,eval_C,eval_C,eval_map,eval_map]
  simp only [eval₂_C_X,mul_comm,sub_self]

variable [IsDomain R]

theorem universalOmission_swap (H L : R[X]) :
    nestedSwap R (universalOmission H L)=universalOmission H L := by
  have e := congrArg (nestedSwap R) (universalOmission_mul H L)
  simp only [map_mul,map_sub,nestedSwap_Y,nestedSwap_C,nestedSwap_map_C,Polynomial.map_X] at e
  apply mul_left_cancel₀ (monic_X_sub_C (X:R[X])).ne_zero
  rw [universalOmission_mul]
  linear_combination -e

theorem universalOmission_outer_cap (H L : R[X]) {n : ℕ}
    (hH : H.natDegree≤n+1) (hL : L.natDegree≤n+1) :
    (universalOmission H L).natDegree≤n := by
  have cap : (C L*H.map (C:R→+*R[X])-C H*L.map C).natDegree≤n+1 :=
    (natDegree_sub_le _ _).trans (max_le
      ((natDegree_C_mul_le _ _).trans (natDegree_map_le.trans hH))
      ((natDegree_C_mul_le _ _).trans (natDegree_map_le.trans hL)))
  unfold universalOmission
  rw [natDegree_divByMonic _ (monic_X_sub_C _),natDegree_X_sub_C]
  omega

theorem universalOmission_coeff_cap (H L : R[X]) {n : ℕ}
    (hH : H.natDegree≤n+1) (hL : L.natDegree≤n+1) (i : ℕ) :
    ((universalOmission H L).coeff i).natDegree≤n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j lt
  have s := swap_coeff_coeff (universalOmission H L) i j
  rw [universalOmission_swap] at s
  rw [s,coeff_eq_zero_of_natDegree_lt ((universalOmission_outer_cap H L hH hL).trans_lt lt)]
  simp

end
end RKCert.FixedPolynomial
