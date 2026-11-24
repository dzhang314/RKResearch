module

public import RKCert.ReviewedNative.OrderedNodalGain
public import RKCert.ReviewedNative.ClockBlockDetection
public import RKCert.ReviewedNative.ReflectedPolynomialBudget
public import RKCert.ReviewedNative.ReverseFlag

@[expose] public section

/-! # Paid reverse clock invariance on reviewed rooted trees

All flags are the actual reviewed adjoint flags. An invariant clock plane
must pay the existing outgoing Hermite gain. The only moment detector is
the native paid Cauchy kernel. No legacy RK proof is imported. -/
namespace RKResearch.Certified.Graded.Reverse
open RKResearch Module Polynomial RKCert.Endpoint
open scoped Matrix

variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
noncomputable section

private theorem weighted_reflected_monomial (k : ℕ) (a : K) :
    weightedEval (reflectedClock A) b (monomial k a) = a • reflectedStageWeight A b k := by
  ext i
  simp only [weightedEval_apply,eval_monomial,Pi.smul_apply,smul_eq_mul,reflectedStageWeight]
  ring

/-- Exactly the reflected scalar polynomial moments, evaluated on the
original clocks, with no claim of order for a reversed RK tableau. -/
theorem reflected_polynomial_mass (ho : HasOrder p A b) (P : K[X]) (pay : P.natDegree+1 ≤ p) :
    (∑ i, weightedEval (reflectedClock A) b P i) = (primitive P).eval 1 := by
  let J : K[X] →ₗ[K] K := (Polynomial.leval 1).comp primitive
  let L : K[X] →ₗ[K] K := (row (1 : Fin s → K)).comp (weightedEval (reflectedClock A) b)
  have mono (k : ℕ) (hk : k ≤ P.natDegree) (a : K) : L (monomial k a) = J (monomial k a) := by
    change row (1 : Fin s → K) (weightedEval (reflectedClock A) b (monomial k a)) = _
    rw [weighted_reflected_monomial,map_smul,smul_eq_mul]
    have row₁ : row (1 : Fin s → K) (reflectedStageWeight A b k) = reflectedProbe A b 0 k 1 := by
      simp only [row_apply,dotProduct,Pi.one_apply,one_mul,mul_one,reflectedProbe,reflectedStageWeight]
      exact Finset.sum_congr rfl (fun i _ => by simp)
    rw [row₁]
    have h := reflected_power_mass ho k (by omega)
    have nz : ((k+1:ℕ):K) ≠ 0 := (IsUnit.of_mul_eq_one _ h).ne_zero
    change a*reflectedProbe A b 0 k 1 = (primitive (monomial k a)).eval 1
    rw [primitive_monomial,eval_monomial,one_pow,mul_one]
    apply (eq_div_iff nz).mpr
    calc
      a*reflectedProbe A b 0 k 1*((k+1:ℕ):K) =
          a*(((k+1:ℕ):K)*reflectedProbe A b 0 k 1) := by ring
      _ = a := by rw [h,mul_one]
  have e : L P = J P := by
    rw [P.as_sum_range' (P.natDegree+1) (by omega),map_sum,map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact mono k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) _
  change (∑ i, weightedEval (reflectedClock A) b P i) = J P
  simpa only [L,LinearMap.comp_apply,row_apply,dotProduct,Pi.one_apply,one_mul] using e

private theorem primitive_shift_sum (P : K[X]) {r : ℕ} (d : P.natDegree ≤ r)
    (origin : P.coeff 0 = 0) (i : ℕ) :
    (primitive (X^i*P)).eval 1 = ∑ j : Fin r, P.coeff j.succ / ((i+j.val+2:ℕ):K) := by
  let T : K[X] →ₗ[K] K :=
    (Polynomial.leval 1).comp (primitive.comp (LinearMap.mulLeft K (X^i:K[X])))
  have h : T P = ∑ j ∈ Finset.range (r+1), P.coeff j / ((i+j+1:ℕ):K) := by
    conv_lhs => rw [P.as_sum_range' (r+1) (by omega),map_sum]
    apply Finset.sum_congr rfl
    intro j _
    change (primitive (X^i*monomial j (P.coeff j))).eval 1 = _
    rw [X_pow_mul_monomial,primitive_monomial,eval_monomial,one_pow,mul_one]
    congr 2
    omega
  rw [←Fin.sum_univ_eq_sum_range,Fin.sum_univ_succ] at h
  simp only [Fin.val_zero,origin,zero_div,zero_add,Fin.val_succ] at h
  exact h

/-- Signed reflected moment budget forces unmatched nonzero clock blocks. -/
theorem reverse_failed_clock_blocks (ho : HasOrder p A b)
    (U : Submodule K (Fin s → K)) (mask : MaskInvariant (reflectedClock A) U)
    (mass : ∀ v∈U, ∑ i, v i = 0) {r : ℕ} (pay : 2*r ≤ p) :
    r ≤ (failedNodes (reflectedClock A) b U s).card := by
  classical
  by_contra! small
  let c := reflectedClock A
  let S := insert 0 (failedNodes c b U s)
  let H := nodalHull S
  have Hd : H.natDegree ≤ r := by
    have ins := Finset.card_insert_le 0 (failedNodes c b U s)
    change (failedNodes c b U s).card < r at small
    change S.card ≤ (failedNodes c b U s).card + 1 at ins
    exact (natDegree_nodalHull S).le.trans (by omega)
  have H0 : H.eval 0=0 := nodalHull_eval_of_mem (Finset.mem_insert_self 0 _)
  have Hc : H.coeff 0=0 := by rw [coeff_zero_eq_eval_zero]; exact H0
  have tests (i : Fin r) :
      (∑ j : Fin r, H.coeff j.succ / ((i.val+j.val+2:ℕ):K))=0 := by
    let Q := X^i.val*H
    have Qd : Q.natDegree+1 ≤ p := by
      have h := natDegree_mul_le (p:=X^i.val) (q:=H)
      rw [natDegree_X_pow] at h
      have hi := i.isLt
      dsimp only [Q]
      omega
    obtain ⟨v,inU,hv⟩ := exists_masked_prefix_lift c b mask s Q
      (by simp [Q,H0]) (fun a ha => by
        have hz : H.eval a=0 := nodalHull_eval_of_mem (S:=S) (Finset.mem_insert_of_mem ha)
        simp [Q,hz])
    have e : v = weightedEval c b Q := by
      ext j
      simpa only [weightedEval_apply] using hv j j.isLt
    have z := mass v inU
    rw [e,reflected_polynomial_mass ho Q Qd,primitive_shift_sum H Hd Hc] at z
    exact z
  have z := moments_detect ho (d:=2) (by decide) (by omega)
    (fun i j : Fin r => by have := i.isLt; have := j.isLt; omega) (fun j : Fin r => H.coeff j.succ) tests
  apply (monic_nodalHull S).ne_zero
  change H=0
  ext k
  rw [coeff_zero]
  cases k with
  | zero => exact Hc
  | succ k =>
    by_cases hk : k < r
    · exact z ⟨k,hk⟩
    · exact coeff_eq_zero_of_natDegree_lt (by omega)

variable [CharZero K]

/-- The actual reflected primitive residual belongs to the very next
all-monomial flag whenever its degree fits the monomial credit. -/
theorem reverse_primitive_next (n : ℕ) (P : K[X]) (d : P.natDegree ≤ n+1) :
    mat A.transpose (weightedEval (reflectedClock A) b P) -
      weightedEval (reflectedClock A) b (primitive P) ∈ primitiveBack A b (n+1) := by
  let W := weightedEval (reflectedClock A) b
  let D := (mat A.transpose).comp W-W.comp primitive
  have mono (k : ℕ) (hk : k ≤ n+1) (a : K) : D (monomial k a) ∈ primitiveBack A b (n+1) := by
    have nz : ((k+1:ℕ):K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    have paid : reflectedStageRow A b k ∈ primitiveBack A b (n+1) :=
      adjointFlag_credit (monomialCredit A b) n (monomial_mem_credit n k hk)
    have h := (primitiveBack A b (n+1)).smul_mem (a/((k+1:ℕ):K)) paid
    rw [reflectedStageRow,smul_sub,smul_smul,div_mul_cancel₀ _ nz] at h
    change mat A.transpose (W (monomial k a)) - W (primitive (monomial k a)) ∈ _
    rw [primitive_monomial,show W=weightedEval (reflectedClock A) b from rfl,
      weighted_reflected_monomial,weighted_reflected_monomial,map_smul]
    exact h
  change D P ∈ _
  rw [P.as_sum_range' (n+2) (by omega),map_sum]
  exact (primitiveBack A b (n+1)).sum_mem fun k hk => mono k (by have := Finset.mem_range.mp hk; omega) _

/-- Genuine outgoing Hermite gain for a clock-invariant reverse flag. -/
theorem reverse_clock_invariant_gain (ha : ∀ i j, i ≤ j → A i j=0)
    (ho : HasOrder p A b) (n : ℕ) (pay : n+2 ≤ p)
    (inv : (primitiveBack A b n).map (diag (reflectedClock A)) ≤ primitiveBack A b n) :
    finrank K (primitiveBack A b n)+(n+2)/2 ≤ finrank K (primitiveBack A b (n+1)) := by
  let U := primitiveBack A b n
  let Z := primitiveBack A b (n+1)
  let r := (n+2)/2
  have mask : MaskInvariant (reflectedClock A) U :=
    clock_mask_invariant (fun _ hv => inv (Submodule.mem_map_of_mem hv))
  have mass (v : Fin s → K) (hv : v∈U) : ∑ i,v i=0 := by
    have h := mem_annih.mp (primitiveBack_annih ho 0 n (by omega) hv) _ (one_mem_treeSpace A 0)
    simpa only [row_apply,dotProduct,Pi.one_apply,mul_one] using h
  have rr : 2*r ≤ n+2 := by dsimp [r]; omega
  have enough := reverse_failed_clock_blocks ho U mask mass (rr.trans pay)
  exact ordered_hermite_outgoing Fin.revPerm _ (causal_transpose ha) (reflectedClock A) b U Z
    mask (adjointFlag_le_succ _ _) (fun _ hv => adjointFlag_transpose _ _ (Submodule.mem_map_of_mem hv))
    r enough (fun P hp => reverse_primitive_next n P (by omega))

end
end RKResearch.Certified.Graded.Reverse
