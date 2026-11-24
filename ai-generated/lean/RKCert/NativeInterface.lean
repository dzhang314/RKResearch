module
public import RKCert.FreeQuasiGate
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.RingTheory.Polynomial.ShiftedLegendre

@[expose] public section

/-! # Pinned Mathlib interfaces for the two-endpoint certificate

The coefficient-vector proofs evaluate the actual polynomial ofFn.  The free
pencil is the mapped derivative of Mathlib's shifted Legendre polynomial,
with the sign change at odd degree due to its 1-2x convention. -/

namespace RKCert.Endpoint
open Polynomial
open scoped Classical
variable {K : Type*} [Field K] [CharZero K]
noncomputable section

omit [CharZero K] in
/-- The finite Horner/power-sum encoding is the evaluation of the native polynomial. -/
theorem value_eq_eval_ofFn {n : ℕ} (c : Fin n → K) (x : K) :
    value c x = (Polynomial.ofFn n c).eval x := by
  rw [Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial, value]

/-- Native polynomial in K[X] from the existing integer Legendre derivative. -/
def nativeDerivative (n : ℕ) : K[X] :=
    (Polynomial.shiftedLegendre n).derivative.map (Int.castRingHom K)

omit [CharZero K] in
private lemma evalShift (n : ℕ) (x : K) :
    (nativeDerivative (K := K) (n+1)).eval x =
    ∑ k ∈ Finset.range (n+1), (((((Polynomial.shiftedLegendre (n+1)).derivative).coeff k) : ℤ):K)*x^k := by
  let p := (Polynomial.shiftedLegendre (n+1)).derivative
  have hd : p.natDegree < n+1 := by
    dsimp [p]; rw [Polynomial.natDegree_derivative,Polynomial.natDegree_shiftedLegendre]; omega
  have pc := congrArg (fun r : ℤ[X] => (r.map (Int.castRingHom K)).eval x) (p.as_sum_range' (n+1) hd)
  simpa [nativeDerivative,p,Polynomial.map_sum,Polynomial.eval_finsetSum,Polynomial.map_monomial] using pc

theorem jacDerivative7_native (x : K) :
    jacDerivative7 x = (nativeDerivative 8).eval x := by
  rw [show 8 = 7+1 by decide, evalShift]
  norm_num [Polynomial.coeff_derivative, Polynomial.coeff_shiftedLegendre,
    Finset.sum_range_succ, Nat.choose, jacDerivative7]
  ring

theorem jacDerivative8_native (x : K) :
    jacDerivative8 x = -(nativeDerivative 9).eval x := by
  rw [show 9 = 8+1 by decide, evalShift]
  norm_num [Polynomial.coeff_derivative, Polynomial.coeff_shiftedLegendre,
    Finset.sum_range_succ, Nat.choose, jacDerivative8]
  ring

/-- The actual native polynomial pencil used by the order-17 finite obstruction. -/
def nativePencil (u t : K) : K[X] :=
  -(nativeDerivative 9).comp (C u * X) + C t * (nativeDerivative 8).comp (C u * X)

theorem nativePencil_eval (u t x : K) :
    (nativePencil u t).eval x = jacDerivative8 (u*x) + t*jacDerivative7 (u*x) := by
  simp [nativePencil, jacDerivative7_native,jacDerivative8_native, Polynomial.eval_comp]

omit [CharZero K] in
private lemma degreePencil (u t : K) (hu : u ≠ 0) : (nativePencil u t).natDegree ≤ 8 := by
  have lin : (C u * X).natDegree = 1 := by simp [hu]
  have bd (n : ℕ) : ((nativeDerivative (K:=K) n).comp (C u*X)).natDegree ≤ n-1 := by
    apply Polynomial.natDegree_comp_le.trans
    rw [lin,mul_one]
    apply Polynomial.natDegree_map_le.trans
    rw [Polynomial.natDegree_derivative,Polynomial.natDegree_shiftedLegendre]
  apply (Polynomial.natDegree_add_le ..).trans
  apply max_le
  · simpa only [natDegree_neg] using bd 9
  · exact (Polynomial.natDegree_C_mul_le _ _).trans ((bd 8).trans (by decide))

/-- Same free-θ obstruction stated with native divisibility, without assuming
the quotient exists in a prescribed coefficient format. -/
theorem freeQuasi17_polynomial_divisor (c : Fin 5 → K) (a u t : K)
    (ha : a ≠ 0) (ha1 : a ≠ 1) (hu : u ≠ 0) (h : twoTests c a 3)
    (hd : (X-C 1)*(X-C a)*Polynomial.ofFn 5 c ∣ nativePencil u t) : c = 0 := by
  by_cases h4 : c 4 = 0
  · let v : Fin 4 → K := fun j => c j.castSucc
    have e (x : K) (k : ℕ) : moment v x k = moment c x k := by
      simp [v,moment,Fin.sum_univ_succ,h4]
    have vh : twoTests v a 3 :=
      ⟨fun k => (e _ _).trans (h.1 k),by rw [e,e];exact h.2.1,by rw [e,e];exact h.2.2⟩
    have z := match3 v a ha ha1 vh
    have zv (j : Fin 4) : c j.castSucc = 0 := congrFun z j
    funext i; fin_cases i
    · exact zv 0
    · exact zv 1
    · exact zv 2
    · exact zv 3
    · exact h4
  obtain ⟨q,hq⟩ := hd
  apply freeQuasi17_quartic_gate c a u t ha ha1 hu h
  have eqeval (x : K) : jacDerivative8 (u*x)+t*jacDerivative7 (u*x) =
      (x-1)*(x-a)*value c x*q.eval x := by
    rw [← nativePencil_eval, hq, value_eq_eval_ofFn]; simp
  by_cases z : q = 0
  · exact ⟨0,0,0,fun x => by simpa [z] using eqeval x⟩
  have dc : (Polynomial.ofFn 5 c).natDegree = 4 := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · have e := Polynomial.ofFn_natDegree_lt (by decide : 1 ≤ 5) c
      omega
    · simpa [Polynomial.ofFn_coeff_eq_val_of_lt c (by decide : 4 < 5)] using h4
  have nz : Polynomial.ofFn 5 c ≠ 0 := by intro zz; simp [zz] at dc
  have nab : (X-C (1:K))*(X-C a) ≠ 0 := mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
  have total := degreePencil u t hu
  rw [hq, natDegree_mul (mul_ne_zero nab nz) z, natDegree_mul nab nz,
    natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _), dc, natDegree_X_sub_C,
    natDegree_X_sub_C] at total
  have qd : q.natDegree < 3 := by omega
  refine ⟨q.coeff 0,q.coeff 1,q.coeff 2,fun x => ?_⟩
  rw [eqeval x]
  congr 1
  have eqp := congrArg (fun r : K[X] => r.eval x) (q.as_sum_range' 3 qd)
  simpa [Finset.sum_range_succ, Polynomial.eval_finsetSum] using eqp

end
end RKCert.Endpoint

