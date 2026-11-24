module
public import RKCert.ReviewedNative.OrderNineMultiSix
public import RKCert.ReviewedNative.MergeEqualRows

@[expose] public section

/-! # Physical cohort adjoints in the original reviewed tableau
The adjoint with unreflected clock powers is obtained directly from the
native reflected polynomial theorem. No old order predicate is imported
at the theorem boundary and no quotient tableau is used. -/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Polynomial Module OneOff Reverse RKCert.Endpoint
open scoped Matrix Classical

variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}

abbrev transMat (A : Matrix (Fin s) (Fin s) K) := mat A.transpose

theorem row_sub_col (v w x : Fin s→K) : row (v-w) x=row v x-row w x := by
  rw [row_apply,dotProduct_comm,←row_apply,map_sub,row_apply x v,row_apply x w,
    dotProduct_comm x v,dotProduct_comm x w]
  rfl
theorem row_smul_col (z : K) (v x : Fin s→K) : row (z • v) x=z*row v x := by
  simp only [row_apply,dotProduct,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]
theorem row_single_eq_coord (w : Fin s→K) (i : Fin s) : row w (Pi.single i 1)=w i :=
  (coordinate_as_single (K:=K) i) ▸ Reverse.row_coordinate w i
theorem row_single_left_eq_coord (w : Fin s→K) (i : Fin s) : row (Pi.single i 1) w=w i := by
  rw [row_apply,dotProduct_comm,←row_apply,row_single_eq_coord]
theorem row_flip_mat (A : Matrix (Fin s) (Fin s) K) (v w : Fin s→K) :
    row (transMat A v) w=row v (mat A w) := Reverse.row_mat_transpose A v w
theorem row_flip_diag (c v w : Fin s→K) : row (diag c v) w=row v (diag c w) := Reverse.row_diag c v w

theorem ones_clock (ho : HasOrder A b p) (pay : 2≤p) :
    row (diag (reflectedClock A) b) (1 : Fin s→K) = (2:K)⁻¹ := by
  have e : row (diag (reflectedClock A) b) (1 : Fin s→K)=reflectedProbe A b 0 1 1 := by
    simp only [row_apply,dotProduct,diag_apply,Pi.one_apply,pow_zero,pow_one,mul_one]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [e]
  have h := reflected_power_mass ho 1 (by omega)
  exact (IsUnit.of_mul_eq_one _ h).mul_left_cancel (h.trans
    (mul_inv_cancel₀ (IsUnit.of_mul_eq_one _ h).ne_zero).symm)

def orderAdjoint (A : Matrix (Fin s) (Fin s) K) (b : Fin s→K) (k : ℕ) : Fin s→K :=
  transMat A (fun i=>b i*nodes A i^k) -
    (((k+1:ℕ):K)⁻¹ : K) • (fun i=>b i*(1-nodes A i^(k+1)))

theorem orderAdjoint_zero_eq_D1 (A : Matrix (Fin s) (Fin s) K) (b : Fin s→K) :
    orderAdjoint A b 0 = firstSeed A b := by
  have a : reflectedStageWeight A b 0=b := by ext i; simp [reflectedStageWeight]
  have c : reflectedStageWeight A b 1=(fun i=>b i*(1-nodes A i)) := by
    ext i; simp [reflectedStageWeight,reflectedClock]
  simp only [orderAdjoint,firstSeed,reflectedStageRow,a,c,pow_zero,mul_one,zero_add,
    pow_one,Nat.cast_one,inv_one,one_smul]
  rfl

theorem orderAdjoint_of_D1 (hD : firstSeed A b=0) (k : ℕ) :
    orderAdjoint A b k =
      -transMat A (fun i=>b i*(1-nodes A i^k)) +
        (fun i=>b i*((1-nodes A i)-(1-nodes A i^(k+1))/((k+1:ℕ):K))) := by
  have hB : transMat A b = diag (reflectedClock A) b := by
    rw [←orderAdjoint_zero_eq_D1,orderAdjoint] at hD
    ext i
    have e := congrFun (sub_eq_zero.mp hD) i
    simpa only [pow_zero,pow_one,mul_one,zero_add,Nat.cast_one,inv_one,one_smul,diag_apply,
      reflectedClock,Pi.sub_apply,Pi.one_apply,mul_comm] using e
  have hA : (fun i=>b i*nodes A i^k)=b-(fun i=>b i*(1-nodes A i^k)) := by
    ext i; simp only [Pi.sub_apply]; ring
  rw [orderAdjoint,hA,map_sub,hB]
  ext i
  simp only [Pi.sub_apply,Pi.add_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
    diag_apply,reflectedClock,Pi.one_apply,div_eq_mul_inv]
  ring

theorem orderAdjoint_one_eq_backward_two (hD : firstSeed A b=0) (h2 : (2:K)≠0) :
    orderAdjoint A b 1 = -((2:K)⁻¹ : K) • quadraticSeed A b := by
  have e : (fun i=>b i*(1-nodes A i^1))=reflectedStageWeight A b 1 := by
    ext i; simp [reflectedStageWeight,reflectedClock]
  rw [orderAdjoint_of_D1 hD,e,quadraticSeed,reflectedStageRow]
  ext i
  simp only [Pi.sub_apply,Pi.add_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
    reflectedStageWeight,reflectedClock,Pi.one_apply,Nat.reduceAdd,Nat.cast_ofNat,div_eq_mul_inv,
    transMat,mat_apply]
  field_simp
  ring

private theorem unreflected_primitive [CharZero K] (k : ℕ) :
    primitive ((1-X:K[X])^k) = ((k+1:ℕ):K)⁻¹ • (1-(1-X)^(k+1)) := by
  let P : K[X] := ((k+1:ℕ):K)⁻¹ • (1-(1-X)^(k+1))
  have h0 : P.coeff 0=0 := by
    rw [coeff_zero_eq_eval_zero]
    simp [P]
  have hd : P.derivative=(1-X)^k := by
    have nz : ((k+1:ℕ):K)≠0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    change (((k+1:ℕ):K)⁻¹ • (1-(1-X:K[X])^(k+1))).derivative=_
    rw [derivative_smul,derivative_sub,derivative_one,derivative_pow_succ,
      derivative_sub,derivative_one,derivative_X]
    simp only [zero_sub,mul_neg,mul_one,neg_neg,Polynomial.smul_eq_C_mul]
    rw [←mul_assoc,←map_mul,←show ((k+1:ℕ):K)=(k:K)+1 by simp,inv_mul_cancel₀ nz,map_one,one_mul]
  rw [←hd,primitive_derivative P h0]

theorem orderAdjoint_annih [CharZero K] {k j : ℕ}
    (ho : HasOrder A b p) (pay : j+k+2≤p) :
    orderAdjoint A b k ∈ annih (treeSpace A j) := by
  let P := (1-X:K[X])^k
  have dx : (1-X:K[X]).natDegree≤1 := natDegree_sub_le_of_le (show (1:K[X]).natDegree≤1 by simp) (show (X:K[X]).natDegree≤1 by simp)
  have dp : P.natDegree≤k := by simpa only [P,Nat.mul_one] using natDegree_pow_le_of_le k dx
  have e₁ : weightedEval (reflectedClock A) b P = fun i=>b i*nodes A i^k := by
    ext i
    simp [P,reflectedClock,mul_comm]
  have e₂ : weightedEval (reflectedClock A) b (primitive P) =
      (((k+1:ℕ):K)⁻¹ : K) • (fun i=>b i*(1-nodes A i^(k+1))) := by
    ext i
    rw [weightedEval_apply,show primitive P= _ from unreflected_primitive k,Polynomial.eval_smul]
    simp [reflectedClock,mul_left_comm,mul_comm]
  simpa only [orderAdjoint,e₁,e₂] using reverse_primitive_paid ho j P k dp pay

theorem nonzero_orderAdjoint_one [CharZero K] (ha : ∀ i j,i≤j → A i j=0)
    (ho : HasOrder A b p) (pay : 3≤p) (zero : firstSeed A b=0) : orderAdjoint A b 1≠0 := by
  rw [orderAdjoint_one_eq_backward_two zero (by norm_num)]
  apply smul_ne_zero (neg_ne_zero.mpr (inv_ne_zero (by norm_num)))
  intro bad
  have h := back_finrank ha ho 1 (by omega)
  have e : back A b 1=⊥ := by
    change K ∙ firstSeed A b ⊔ (K ∙ firstSeed A b).map (mat A.transpose) ⊔
      (K ∙ firstSeed A b).map (diag (reflectedClock A)) ⊔ K ∙ quadraticSeed A b=⊥
    rw [zero,bad,Submodule.span_singleton_eq_bot.mpr rfl]
    simp
  rw [e,finrank_bot] at h
  omega

theorem transMat_single_incoming_row (A : Matrix (Fin s) (Fin s) K) (i : Fin s) :
    transMat A (Pi.single i 1)=A i := by
  ext j
  simp only [transMat,mat_apply,Matrix.mulVec,dotProduct,Matrix.transpose_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [hk]
  · simp

theorem no_identical_rows_at_uniform_floor {T : Matrix (Fin 12) (Fin 12) K} {w : Fin 12→K}
    (ha : ∀ i j,i≤j → T i j=0) (ho : HasOrder T w 9)
    {i j : Fin 12} (ij : i<j) : ¬ ∀k,T i k=T j k := by
  intro e
  obtain ⟨B,c,hB,hc⟩ := exists_merge_equal_rows ha ho ij e
  have h := odd_midpoint_floor hB hc (q:=4) (by decide) (by decide)
  omega

end RKResearch.Certified.Graded.MultiOff
