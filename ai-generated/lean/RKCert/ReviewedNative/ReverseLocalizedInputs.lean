module
public import RKCert.ReviewedNative.TerminalCapacity
public import RKCert.ReviewedNative.ClockHeadFibers
public import RKCert.ReviewedNative.ReflectedPolynomialBudget
public import RKCert.OrderTwelveReverseObstruction

@[expose] public section

/-! # Literal native inputs for the localized quadratic reverse chart
The only legacy reuse is the tree-free two-node row algebra. The
residuals, pivot and quadrature witnesses use reviewed order. -/
namespace RKResearch.Certified.Graded.Reverse
open RKResearch Polynomial Module RKCert.Endpoint RKCert.ReverseTwoNode RKCert.OneEscape
open RKCert.Paired.OrderTwelve (powerWeight)
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}

abbrev normalizedResidual (A : Matrix (Fin s) (Fin s) K) (b : Fin s→K) (k : ℕ) :=
    (((k+1:ℕ):K)⁻¹ : K) • reflectedStageRow A b k

omit [CharZero K] in
theorem reflected_weights_eq_powerWeight (A : Matrix (Fin s) (Fin s) K) (b : Fin s→K) (k : ℕ) :
    reflectedStageWeight A b k=powerWeight (reflectedClock A) b k := by
  ext i; simp [powerWeight,mul_comm]

theorem normalized_residual_apply (A : Matrix (Fin s) (Fin s) K) (b : Fin s→K) (k : ℕ)
    (i : Fin s) :
    normalizedResidual A b k i=
      mat A.transpose (powerWeight (reflectedClock A) b k) i -
        (reflectedClock A i)^(k+1)*b i/((k+1:ℕ):K) := by
  have nz : ((k+1:ℕ):K)≠0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  unfold normalizedResidual reflectedStageRow
  rw [smul_sub,smul_smul,inv_mul_cancel₀ nz,one_smul,
    reflected_weights_eq_powerWeight,reflected_weights_eq_powerWeight]
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,powerWeight,mat_apply,div_eq_mul_inv]
  ring

omit [CharZero K] in
theorem first_zero_eq_transpose (zero : firstSeed A b=0) :
    mat A.transpose b=diag (reflectedClock A) b := by
  have h0 : reflectedStageWeight A b 0=b := by ext i; simp [reflectedStageWeight]
  have h1 : reflectedStageWeight A b 1=diag (reflectedClock A) b := by ext i; simp [mul_comm]
  change ((0+1:ℕ):K) • mat A.transpose (reflectedStageWeight A b 0) - reflectedStageWeight A b (0+1)=0 at zero
  rw [Nat.zero_add,Nat.cast_one,one_smul,h0,h1] at zero
  exact sub_eq_zero.mp zero

theorem greatest_reflected_pivot (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder p A b)
    (pay : 2≤p) :
    ∃ i : Fin s, reflectedClock A i≠0 ∧ b i≠0 ∧
      (∀ j, i<j → reflectedClock A j*b j=0) ∧
      normalizedResidual A b 1 i= -((2:K)⁻¹)*(reflectedClock A i)^2*b i ∧
      normalizedResidual A b 1 i≠0 := by
  let y := reflectedClock A
  let v := diag y b
  have ht : v≠0 := by
    intro h
    have eq : reflectedProbe A b 0 1 (1 : Fin s→K) = row v 1 := by
      simp only [row_apply,dotProduct,diag_apply,Pi.one_apply,pow_zero,pow_one,mul_one,v]
      exact Finset.sum_congr rfl (fun i _=>mul_comm _ _)
    have e := reflected_power_mass ho 1 (by omega)
    rw [eq,h] at e
    simp at e
  obtain ⟨i,hi⟩ : ∃i,v i≠0 := by by_contra! h; exact ht (funext h)
  let S := Finset.univ.filter (fun j : Fin s=> v j≠0)
  obtain ⟨i,hi,hm⟩ := Finset.exists_max_image S id ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  have hv : y i*b i≠0 := (Finset.mem_filter.mp hi).2
  have before (j : Fin s) (hj : i<j) : v j=0 := by
    by_contra hn
    exact (not_le_of_gt hj) (hm j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩))
  have w1 : powerWeight y b 1=v := by ext j; simp [v,powerWeight]
  have zz : mat A.transpose v i=0 := transpose_tail_zero ha before le_rfl
  have e : normalizedResidual A b 1 i= -((2:K)⁻¹)*(y i)^2*b i := by
    rw [normalized_residual_apply]
    change mat A.transpose (powerWeight y b 1) i- y i^2*b i/2=_
    rw [w1,zz]
    ring
  have nz := mul_ne_zero_iff.mp hv
  have res : normalizedResidual A b 1 i≠0 := by
    rw [e]
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero (by norm_num))) (pow_ne_zero _ nz.1)) nz.2
  exact ⟨i,nz.1,nz.2,before,e,res⟩

omit [CharZero K] in
/-- Any prescribed finite set of reflected clocks smaller than the
available full moment test misses a live physical row. The proof does
not assume positive stage weights or that the clocks lie in an interval. -/
theorem reflected_live_avoid (ho : HasOrder p A b) (T : Finset K) (pay : 2*T.card+1≤p) :
    ∃ i,b i≠0 ∧ reflectedClock A i∉T := by
  by_contra! no
  let S := T.image (fun z=>1-z)
  let H := nodalHull S
  let q := T.card
  have dd : H.natDegree≤q := (natDegree_nodalHull S).le.trans Finset.card_image_le
  let a : Fin (q+1)→K := fun i=>H.coeff i.val
  have zero (k : Fin (q+1)) : probe A b k.val (evalNodes A H)=0 := by
    simp only [probe,row_apply,dotProduct,evalNodes_apply]
    apply Finset.sum_eq_zero
    intro i _
    by_cases bi : b i=0
    · simp [bi]
    · have hc : nodes A i∈S := by
        apply Finset.mem_image.mpr
        refine ⟨reflectedClock A i,no i bi,?_⟩
        simp [reflectedClock]
      rw [show H.eval (nodes A i)=0 from nodalHull_eval_of_mem hc,mul_zero]
  have t (i : Fin (q+1)) : ∑j : Fin (q+1), a j/((i.val+j.val+1:ℕ):K)=0 := by
    have h := zero i
    rw [evalNodes_eq_coeffEval A H dd,probe_coeffEval ho (by have :=i.isLt;change 2*q+1≤p at pay;omega)] at h
    exact h
  have za := moments_detect ho (n:=q+1) (d:=1) (by decide) (by change 2*q+1≤p at pay;omega)
    (fun i j=>by have :=i.isLt; have :=j.isLt; change 2*q+1≤p at pay;omega) a t
  apply (monic_nodalHull S).ne_zero
  ext n
  rw [coeff_zero]
  by_cases le : n≤q
  · exact za ⟨n,by omega⟩
  · exact coeff_eq_zero_of_natDegree_lt (dd.trans_lt (by omega))

end
end RKResearch.Certified.Graded.Reverse
