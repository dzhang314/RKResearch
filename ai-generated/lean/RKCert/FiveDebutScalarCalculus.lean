module

public import RKCert.DirkTrace
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree

@[expose] public section

/-! # Characteristic-zero polynomial calculus for the five-debut obstruction -/
namespace RKCert.FiveDebut
open Polynomial RKCert.Endpoint
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Integration against (x,dx), with the two origin factors removed. -/
def shiftedPrimitive (F : K[X]) : K[X] := (formalPrimitive (X*F)).divX.divX

theorem shiftedPrimitive_mul (F : K[X]) : X^2*shiftedPrimitive F=formalPrimitive (X*F) := by
  let J := formalPrimitive (X*F)
  have h0 : J.coeff 0=0 := by rw [coeff_zero_eq_eval_zero,formalPrimitive_eval_zero]
  have h1 : J.coeff 1=0 := by
    have e := congrArg (fun P : K[X] => P.coeff 0) (derivative_formalPrimitive (X*F))
    change J.derivative.coeff 0=(X*F).coeff 0 at e
    rw [coeff_derivative] at e
    simpa only [Nat.cast_zero,zero_add,mul_one,coeff_X_mul_zero] using e
  have a := X_mul_divX_add J
  have b := X_mul_divX_add J.divX
  rw [h0,map_zero,add_zero] at a
  rw [coeff_divX,h1,map_zero,add_zero] at b
  change X^2*J.divX.divX=J
  rw [pow_two,mul_assoc,b,a]

def eulerTwo (F : K[X]) : K[X] := X*F.derivative+C 2*F

theorem eulerTwo_shifted (F : K[X]) : eulerTwo (shiftedPrimitive F)=F := by
  apply mul_left_cancel₀ (show (X:K[X])≠0 from X_ne_zero)
  calc
    X*eulerTwo (shiftedPrimitive F) = (X^2*shiftedPrimitive F).derivative := by
      rw [eulerTwo,derivative_mul,derivative_X_pow]
      norm_num
      ring
    _ = _ := by rw [shiftedPrimitive_mul,derivative_formalPrimitive]

omit [CharZero K] in
theorem coeff_eulerTwo (F : K[X]) (n : ℕ) :
    (eulerTwo F).coeff n=((n:K)+2)*F.coeff n := by
  rw [eulerTwo,coeff_add,coeff_C_mul]
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_X_mul,coeff_derivative]
    push_cast
    ring

theorem coeff_shiftedPrimitive (F : K[X]) (n : ℕ) :
    (shiftedPrimitive F).coeff n=F.coeff n/((n:K)+2) := by
  have nz : (n:K)+2≠0 := by exact_mod_cast (show n+2≠0 by omega)
  have e := congrArg (fun P : K[X] => P.coeff n) (eulerTwo_shifted F)
  rw [coeff_eulerTwo] at e
  apply (eq_div_iff nz).2
  simpa only [mul_comm] using e

theorem shiftedPrimitive_ne_zero {F : K[X]} (hF : F≠0) : shiftedPrimitive F≠0 := by
  intro e
  apply hF
  have h := eulerTwo_shifted F
  rw [e,eulerTwo,derivative_zero,mul_zero,mul_zero,add_zero] at h
  exact h.symm

theorem shiftedPrimitive_degree (F : K[X]) : (shiftedPrimitive F).natDegree=F.natDegree := by
  by_cases hF : F=0
  · subst F
    have he : shiftedPrimitive (0:K[X])=0 := by
      ext n
      rw [coeff_shiftedPrimitive,coeff_zero,zero_div]
    simp [he]
  · apply natDegree_eq_of_le_of_coeff_ne_zero
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro n hn
      rw [coeff_shiftedPrimitive,coeff_eq_zero_of_natDegree_lt hn,zero_div]
    · rw [coeff_shiftedPrimitive]
      have htop : F.coeff F.natDegree≠0 := by rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hF
      exact div_ne_zero htop (by exact_mod_cast (show F.natDegree+2≠0 by omega))

omit [CharZero K] in
theorem derivative_affine {P : K[X]} (h : P.natDegree≤1) : P.derivative=C (P.coeff 1) := by
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one h]
  simp

omit [CharZero K] in
theorem affine_eval {P : K[X]} (h : P.natDegree≤1) (a : K) :
    P.eval a=P.coeff 1*a+P.coeff 0 := by
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one h]
  simp

omit [CharZero K] in
theorem affine_eq_C_of_coeff_one_zero {P : K[X]} (h : P.natDegree≤1) (h1 : P.coeff 1=0) :
    P=C (P.coeff 0) := by
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one h]
  rw [h1,map_zero,zero_mul,zero_add]

omit [CharZero K] in
theorem affine_natDegree_eq_one {P : K[X]} (h : P.natDegree≤1) :
    P.coeff 1≠0 ↔ P.natDegree=1 := by
  constructor
  · exact natDegree_eq_of_le_of_coeff_ne_zero h
  · intro d hz
    have h0 := congrArg natDegree (affine_eq_C_of_coeff_one_zero h hz)
    rw [d,natDegree_C] at h0
    omega

omit [CharZero K] in
theorem coeff_affine_mul_top (A F : K[X]) {n : ℕ}
    (hA : A.natDegree≤1) (hF : F.natDegree≤n) :
    (A*F).coeff (n+1)=A.coeff 1*F.coeff n := by
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hA,add_mul,mul_assoc]
  rw [coeff_add,coeff_C_mul,coeff_X_mul,coeff_C_mul,
    coeff_eq_zero_of_natDegree_lt (show F.natDegree<n+1 by omega),mul_zero,add_zero]

theorem euler_of_shifted (F A B : K[X])
    (h : shiftedPrimitive F=A*F.derivative+B*F) :
    X*A*F.derivative.derivative+
      (C 2*A+X*(A.derivative+B))*F.derivative+
      (X*B.derivative+C 2*B-1)*F=0 := by
  have e := eulerTwo_shifted F
  simp only [eulerTwo,h,derivative_add,derivative_mul] at e
  linear_combination e

omit [CharZero K] in
theorem eq_of_three_zeros (z : Fin 3→K) (inj : Function.Injective z) (Q : K[X])
    (deg : Q.natDegree≤2) (hz : ∀ i,Q.eval (z i)=0) : Q=0 := by
  classical
  let S := Finset.univ.image z
  have card : S.card=3 := by rw [Finset.card_image_of_injective _ inj,Finset.card_univ,Fintype.card_fin]
  apply eq_of_degrees_lt_of_eval_finset_eq S
  · rw [card]
    exact (degree_le_natDegree).trans_lt (by exact_mod_cast (show Q.natDegree<3 by omega))
  · rw [degree_zero,card]
    exact WithBot.bot_lt_coe (3:ℕ)
  · intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    simpa only [eval_zero] using hz i

end
end RKCert.FiveDebut
