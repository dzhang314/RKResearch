module

public import RKCert.Dirk15SampleLift
public import Mathlib.Algebra.Polynomial.OfFn

@[expose] public section

/-! # Computable small monic remainder by ordinary Horner updates -/
namespace RKCert.Compound
open Polynomial RKCert.FixedPolynomial
open scoped Classical
variable {R : Type*} [CommRing R] [DecidableEq R] [Nontrivial R]

/-- Lower coefficients of the monic modulus are supplied explicitly.
The modulus has one more degree than the number of slots. -/
noncomputable def remainderModulus {n : ℕ} (b : Fin (n+1)→R) : R[X] :=
  X^(n+1)+ofFn (n+1) b

theorem remainderModulus_degree {n : ℕ} (b : Fin (n+1)→R) :
    (remainderModulus b).natDegree=n+1 := by
  unfold remainderModulus
  have lt : (ofFn (n+1) b).natDegree<(X^(n+1):R[X]).natDegree := by
    rw [natDegree_X_pow]
    exact ofFn_natDegree_lt (by omega) _
  rw [natDegree_add_eq_left_of_natDegree_lt lt,natDegree_X_pow]

theorem remainderModulus_monic {n : ℕ} (b : Fin (n+1)→R) : (remainderModulus b).Monic := by
  have dg := remainderModulus_degree b
  rw [Monic,leadingCoeff,dg,remainderModulus,coeff_add,coeff_X_pow_self,ofFn_coeff_eq_zero_of_ge _ le_rfl,add_zero]

/-- One Horner step discards the degree-(n+1) term by one copy
of the monic modulus. -/
def remainderStep {n : ℕ} (b r : Fin (n+1)→R) (a : R) (i : Fin (n+1)) : R :=
  (if zi : i.val=0 then a else r ⟨i.val-1,by have :=i.isLt; omega⟩)-
    r (Fin.last n)*b i

omit [Nontrivial R] in
theorem remainderStep_exact {n : ℕ} (b r : Fin (n+1)→R) (a : R) :
    ofFn (n+1) (remainderStep b r a)=
      C a+X*ofFn (n+1) r-C (r (Fin.last n))*remainderModulus b := by
  ext j
  rcases j with _|j
  · have h : (0:ℕ)<n+1 := by omega
    rw [ofFn_coeff_eq_val_of_lt _ h,coeff_sub,coeff_add,coeff_C_zero,coeff_X_mul_zero,coeff_C_mul,
      remainderModulus,coeff_add,coeff_X_pow,ite_eq_right (by omega),zero_add,ofFn_coeff_eq_val_of_lt _ h,
      add_zero]
    simp [remainderStep]
  have hh : (C a+X*ofFn (n+1) r-C (r (Fin.last n))*remainderModulus b).coeff (j+1)=
      (ofFn (n+1) r).coeff j-r (Fin.last n)*
        ((X^(n+1):R[X]).coeff (j+1)+(ofFn (n+1) b).coeff (j+1)) := by
    rw [coeff_sub,coeff_add,coeff_C_succ,coeff_X_mul,zero_add,coeff_C_mul,remainderModulus,coeff_add]
  rw [hh]
  by_cases small : j+1<n+1
  · have lt : j<n+1 := by omega
    rw [ofFn_coeff_eq_val_of_lt _ small,ofFn_coeff_eq_val_of_lt _ small,
      ofFn_coeff_eq_val_of_lt _ lt,coeff_X_pow,ite_eq_right (by omega),zero_add]
    simp [remainderStep]
  · rw [ofFn_coeff_eq_zero_of_ge (remainderStep b r a) (by omega),
      ofFn_coeff_eq_zero_of_ge b (i:=j+1) (by omega),add_zero]
    by_cases endj : j=n
    · subst j
      rw [coeff_X_pow_self,ofFn_coeff_eq_val_of_lt _ (by omega),mul_one]
      change (0:R)=r (Fin.last n)-r (Fin.last n)
      rw [sub_self]
    · rw [coeff_X_pow,ite_eq_right (by omega),mul_zero,sub_zero,
        ofFn_coeff_eq_zero_of_ge _ (by omega)]

def residueHornerRemainder {n : ℕ} (b : Fin (n+1)→R) (c : List R) : Fin (n+1)→R :=
  c.foldr (fun a r => remainderStep b r a) 0

theorem residueHornerRemainder_exact {n : ℕ} (b : Fin (n+1)→R) (c : List R) :
    (ofCoeffList c)%ₘ(remainderModulus b)=ofFn (n+1) (residueHornerRemainder b c) := by
  have div : remainderModulus b∣ofCoeffList c-ofFn (n+1) (residueHornerRemainder b c) := by
    induction c with
    | nil => simp [residueHornerRemainder]
    | cons a t ih =>
      have step : residueHornerRemainder b (a::t)=remainderStep b (residueHornerRemainder b t) a := rfl
      rw [step,remainderStep_exact,ofCoeffList_cons]
      have key :
          (C a+X*ofCoeffList t) -
            (C a+X*ofFn (n+1) (residueHornerRemainder b t)-
              C (residueHornerRemainder b t (Fin.last n))*remainderModulus b)=
          X*(ofCoeffList t-ofFn (n+1) (residueHornerRemainder b t))+
            C (residueHornerRemainder b t (Fin.last n))*remainderModulus b := by ring
      rw [key]
      exact (ih.mul_left _).add (dvd_mul_left _ _)
  rw [modByMonic_eq_of_dvd_sub (remainderModulus_monic b) div]
  apply (modByMonic_eq_self_iff (remainderModulus_monic b)).mpr
  rw [degree_eq_natDegree (remainderModulus_monic b).ne_zero,remainderModulus_degree]
  exact ofFn_degree_lt _

/-- Eager array form; each step evaluates each coefficient once instead
of nesting an entirely unevaluated function in the next Horner closure. -/
def residueRemainderArray {n : ℕ} (b : Fin (n+1)→R) (c : List R) : Array R :=
  c.foldr (fun a r => Array.ofFn (remainderStep b (fun i => r[i.val]?.getD 0) a))
    (Array.replicate (n+1) 0)

omit [Nontrivial R] in
theorem residueRemainderArray_at {n : ℕ} (b : Fin (n+1)→R) (c : List R) (i : Fin (n+1)) :
    (residueRemainderArray b c)[i.val]?.getD 0=residueHornerRemainder b c i := by
  induction c generalizing i with
  | nil => simp [residueRemainderArray,residueHornerRemainder,i.isLt]
  | cons a c ih =>
    change (Array.ofFn (remainderStep b (fun t =>
      (residueRemainderArray b c)[t.val]?.getD 0) a))[i.val]?.getD 0=
        remainderStep b (residueHornerRemainder b c) a i
    have e : (fun t : Fin (n+1) => (residueRemainderArray b c)[t.val]?.getD 0)=residueHornerRemainder b c :=
      funext (fun i => ih i)
    rw [e]
    simp [i.isLt]

omit [Nontrivial R] in
theorem low_coeff_of_remainderModulus {n : ℕ} (b : Fin (n+1)→R) (i : Fin (n+1)) :
    (remainderModulus b).coeff i.val=b i := by
  rw [remainderModulus,coeff_add,coeff_X_pow,ite_eq_right (by have :=i.isLt; omega),zero_add,
    ofFn_coeff_eq_val_of_lt _ i.isLt]

end RKCert.Compound
