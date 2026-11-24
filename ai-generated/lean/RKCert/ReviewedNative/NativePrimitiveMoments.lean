module

public import RKCert.ReviewedNative.FiniteCauchy
public import RKCert.ReviewedNative.WeightedClockBand
public import RKCert.ReviewedNative.GradedPrimitives

@[expose] public section

/-! # Exact unit moments with an endpoint equation

The beta moment kernel is an ordinary Cauchy system fed one extra row.
For a polynomial with both endpoints zero, the added row at index −1
is precisely the sum-of-coefficients endpoint condition. This requires
no positivity or tabulated matrix computation. -/
namespace RKResearch.Certified.Graded.NativeMoments
open Polynomial
open scoped Classical

variable {K : Type*} [Field K]
set_option maxRecDepth 3500
set_option maxHeartbeats 650000

private theorem primitive_moment_ofFn {n : ℕ} (a : Fin n→K) (i d : ℕ) :
    (primitive (X^i*(X^d*ofFn n a))).eval 1 =
      ∑ j : Fin n, a j/((i+j.val+d+1:ℕ):K) := by
  rw [←mul_assoc,←pow_add,ofFn_eq_sum_monomial,Finset.mul_sum,map_sum,eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  rw [X_pow_mul_monomial,primitive_monomial,eval_monomial,one_pow,mul_one]
  congr 2
  omega

variable [CharZero K]

/-- Consecutive moment tests against X times the polynomial separate its
actual degree band; there is no sign assumption on the original weights. -/
theorem x_moments_detect {P : K[X]} {n : ℕ} (d : P.natDegree≤n)
    (test : ∀ i : Fin (n+1), (primitive (X^i.val*(X*P))).eval 1=0) : P=0 := by
  let a : Fin (n+1)→K := toFn (n+1) P
  have e : ofFn (n+1) a=P := ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  let x : Fin (n+1) → K := fun i => (i.val:K)
  let y : Fin (n+1) → K := fun j => ((j.val+2:ℕ):K)
  have xi : Function.Injective x := fun _ _ h => Fin.ext (Nat.cast_injective h)
  have yi : Function.Injective y := by
    intro i j h
    have z : i.val+2=j.val+2 := Nat.cast_injective h
    exact Fin.ext (by omega)
  have nz (i j : Fin (n+1)) : x i+y j≠0 := by
    dsimp [x,y]
    rw [←Nat.cast_add]
    exact Nat.cast_ne_zero.mpr (by omega)
  have m (i : Fin (n+1)) : (∑ j : Fin (n+1), a j/(x i+y j))=0 := by
    have t := test i
    rw [←e,show (X:K[X])*ofFn (n+1) a=X^1*ofFn (n+1) a by rw [pow_one],
      primitive_moment_ofFn] at t
    convert t using 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    dsimp [x,y]
    rw [←Nat.cast_add]
    congr 1
  have z := cauchy_kernel x y a xi yi nz m
  rw [←e,show a=0 from funext z,map_zero]

/-- At an extra artificial index −1 the rescaled coefficient row is
exactly the endpoint equation, so it completes the finite Cauchy system. -/
private theorem extra_row_cauchy {n : ℕ} (a : Fin (n+1)→K) (mass : (∑ j,a j)=0)
    (tests : ∀ i : Fin n, (∑ j : Fin (n+1), a j/((i.val+j.val+2:ℕ):K))=0) :
    ∀ j,a j=0 := by
  let y : Fin (n+1)→K := fun j => ((j.val+2:ℕ):K)
  let x : Fin (n+1)→K := Fin.cases (-1) (fun i : Fin n => (i.val:K))
  let a' : Fin (n+1)→K := fun j => (y j-1)*a j
  have cast_ne (i : Fin n) : (i.val:K)≠ -1 := by
    intro h
    apply (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero i.val) : ((i.val+1:ℕ):K)≠0)
    rw [Nat.cast_add,Nat.cast_one,h,neg_add_cancel]
  have hx : Function.Injective x := by
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases (fun _ => rfl) (fun j h => ?_) j
      exact (cast_ne j (by simpa only [x,Fin.cases_zero,Fin.cases_succ] using h.symm)).elim
    · refine Fin.cases (fun h => ?_) (fun j h => ?_) j
      · exact (cast_ne i (by simpa only [x,Fin.cases_zero,Fin.cases_succ] using h)).elim
      · have e : (i.val:K)=(j.val:K) := by simpa only [x,Fin.cases_succ] using h
        exact congrArg Fin.succ (Fin.ext (Nat.cast_injective e))
  have hy : Function.Injective y := by
    intro i j h
    have e : i.val+2=j.val+2 := Nat.cast_injective h
    exact Fin.ext (by omega)
  have ny (j : Fin (n+1)) : y j-1≠0 := by
    have e : y j-1 = (((j.val+1:ℕ):K)) := by dsimp [y]; push_cast; ring
    rw [e]
    exact Nat.cast_ne_zero.mpr (by omega)
  have nz (i j : Fin (n+1)) : x i+y j≠0 := by
    refine Fin.cases ?_ (fun i => ?_) i
    · change -1+y j≠0
      rw [add_comm,←sub_eq_add_neg]
      exact ny j
    · simp only [x,Fin.cases_succ,y,←Nat.cast_add]
      exact Nat.cast_ne_zero.mpr (by omega)
  have test (i : Fin (n+1)) : (∑ j : Fin (n+1), a' j/(x i+y j))=0 := by
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [←mass]
      apply Finset.sum_congr rfl
      intro j _
      change (y j-1)*a j/(-1+y j)=a j
      rw [add_comm,←sub_eq_add_neg,mul_comm,mul_div_cancel_right₀ _ (ny j)]
    · have t : (∑ j : Fin (n+1), a j/(x i.succ+y j))=0 := by
        simpa only [x,Fin.cases_succ,y,←Nat.cast_add,Nat.add_assoc] using tests i
      have split (j : Fin (n+1)) :
          a' j/(x i.succ+y j)=a j-(x i.succ+1)*(a j/(x i.succ+y j)) := by
        dsimp only [a']
        field_simp [nz i.succ j]
        ring
      simp_rw [split,Finset.sum_sub_distrib,←Finset.mul_sum,mass,t,mul_zero,sub_zero]
  intro j
  exact (mul_eq_zero.mp (cauchy_kernel x y a' hx hy nz test j)).resolve_left (ny j)

/-- N moments of (1−X)·P plus P(0)=0 detect a polynomial of degree ≤N in
any characteristic-zero field; the endpoint at 1 is automatic. -/
theorem endpoint_moments_detect {P : K[X]} {n : ℕ} (d : P.natDegree≤n)
    (origin : P.eval 0=0)
    (paid : ∀ i : Fin n, (primitive (X^i.val*((1-X)*P))).eval 1=0) : P=0 := by
  let H : K[X] := (1-X)*P
  let a : Fin (n+1)→K := fun j => H.coeff (j.val+1)
  have hD : H.natDegree≤n+1 := by
    have leOne : (1-X:K[X]).natDegree≤1 := natDegree_sub_le_of_le (show (1:K[X]).natDegree≤1 by simp)
      (show (X:K[X]).natDegree≤1 by simp)
    exact natDegree_mul_le_of_le leOne d |>.trans (by omega)
  have e : H=X*ofFn (n+1) a := by
    ext i
    cases i with
    | zero => simp [coeff_zero_eq_eval_zero,H,origin]
    | succ i =>
      rw [coeff_X_mul]
      by_cases h : i<n+1
      · exact (ofFn_coeff_eq_val_of_lt a h).symm
      · rw [coeff_eq_zero_of_natDegree_lt (hD.trans_lt (by omega)),
          ofFn_coeff_eq_zero_of_ge a (by omega)]
  have mass : (∑ j,a j)=0 := by
    have f := congrArg (eval (1:K)) e
    simp only [H,eval_mul,eval_sub,eval_one,eval_X,sub_self,zero_mul,one_mul,
      ofFn_eq_sum_monomial,eval_finsetSum,eval_monomial,one_pow,mul_one] at f
    exact f.symm
  have tst (i : Fin n) : (∑ j : Fin (n+1), a j/((i.val+j.val+2:ℕ):K))=0 := by
    have t := paid i
    change (primitive (X^i.val*H)).eval 1=0 at t
    rw [e,show (X:K[X])*ofFn (n+1) a=X^1*ofFn (n+1) a by rw [pow_one],
      primitive_moment_ofFn] at t
    simpa only [Nat.add_assoc,Nat.reduceAdd] using t
  have z := extra_row_cauchy a mass tst
  rw [show a=0 from funext z,map_zero,mul_zero] at e
  apply (mul_eq_zero.mp e).resolve_left
  rw [show (1-X:K[X])=-(X-C (1:K)) by simp]
  exact neg_ne_zero.mpr (X_sub_C_ne_zero _)

end RKResearch.Certified.Graded.NativeMoments
