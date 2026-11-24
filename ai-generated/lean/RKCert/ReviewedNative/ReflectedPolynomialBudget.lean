module
public import RKCert.ReviewedNative.ReflectedMoments
public import RKCert.ReviewedNative.GradedPrimitives

@[expose] public section

/-! # Reflected polynomial probes of the actual reviewed order -/
namespace RKResearch.Certified.Graded
open RKResearch FiniteRootedTree Polynomial
open scoped Matrix FiniteRootedTree

variable {ι K : Type*} [Fintype ι] [Field K]
variable {A : Matrix ι ι K} {b : ι → K} {p j : ℕ}

theorem reflectedProbe_zeroSpace (ho : HasOrder A b p) (r k : ℕ)
    {v : ι → K} (hv : v ∈ zeroSpace A j) (pay : r+k+j+1 ≤ p) :
    reflectedProbe A b r k v=0 := by
  induction k generalizing r with
  | zero =>
    rw [reflectedProbe_zero_right]
    exact probe_zeroSpace ho (by omega) hv
  | succ k ih =>
    rw [reflectedProbe_succ_right,ih r (by omega),ih (r+1) (by omega),sub_self]

theorem reflectedProbe_evalNodes (ho : HasOrder A b p) (P : K[X]) (r k : ℕ)
    (pay : r+k+P.natDegree+1 ≤ p) :
    reflectedProbe A b r k (evalNodes A P) =
      (primitive (X^r*((1-X)^k*P))).eval 1 := by
  let H : K[X] := (1-X)^k
  have leOne : (1-X : K[X]).natDegree≤1 :=
    natDegree_sub_le_of_le (show (1:K[X]).natDegree≤1 by simp)
      (show (X:K[X]).natDegree≤1 by simp)
  have hdeg : H.natDegree≤k := by
    simpa only [H,Nat.mul_one] using natDegree_pow_le_of_le k leOne
  have dP : (H*P).natDegree≤k+P.natDegree := natDegree_mul_le_of_le hdeg le_rfl
  have eq : reflectedProbe A b r k (evalNodes A P)=probe A b r (evalNodes A (H*P)) := by
    simp only [reflectedProbe,probe,row_apply,dotProduct,evalNodes_apply,reflectedClock,
      Pi.sub_apply,Pi.one_apply,H,eval_mul,eval_pow,eval_sub,eval_one,eval_X]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [eq,probe_evalNodes ho (H*P) r (by omega)]

/-- The forward defect pairs to zero at the whole reflected degree budget. -/
theorem reflectedProbe_primitive_of_defect (ho : HasOrder A b p) (r k : ℕ)
    (pay : r+k+j+1 ≤ p) {P : K[X]} (dP : P.natDegree ≤ j) {f : ι → K}
    (hf : f-evalNodes A P ∈ zeroSpace A j) :
    reflectedProbe A b r k f = (primitive (X^r*((1-X)^k*P))).eval 1 := by
  have h := reflectedProbe_zeroSpace ho r k hf pay
  rw [map_sub,sub_eq_zero] at h
  exact h.trans (reflectedProbe_evalNodes ho P r k (by omega))

/-- Exact reflected bush moments, with no sign assumptions on b or the nodes. -/
theorem reflected_power_mass (ho : HasOrder A b p) (k : ℕ) (pay : k+1 ≤ p) :
    ((k+1:ℕ):K) * reflectedProbe A b 0 k 1 = 1 := by
  induction k with
  | zero =>
    have h := probe_normTree ho .leaf 0 (by simpa using pay)
    simpa [order] using h
  | succ k ih =>
    have low := ih (by omega)
    have sh := reflectedProbe_norm_shift ho .leaf 0 k (by simp [order]; omega)
    have eq := reflectedProbe_succ_right A b 0 k 1
    simp only [order,PNat.one_coe,Nat.add_zero,Nat.zero_add,Nat.cast_one,one_mul,normTree_leaf] at sh
    simp only [Nat.cast_add,Nat.cast_one] at low sh ⊢
    linear_combination low - sh + ((k:K)+1)*eq

end RKResearch.Certified.Graded
