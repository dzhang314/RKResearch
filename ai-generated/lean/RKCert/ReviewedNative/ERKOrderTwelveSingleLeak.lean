module

public import RKCert.ReviewedNative.ERKOrderTwelveRankTwoThree

public section

/-! # The one remaining terminal-zero grade-eight leakage direction

A normalized degree-six profile has two actual endpoint zeros and four
paid ordinary row probes. Subtract a single degree-six direction and
apply native two-endpoint separation, without a degree-specific decoder.
-/
namespace RKResearch.Certified.Graded.ERK12

open RKResearch Polynomial Module Reverse
open scoped Matrix

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}

private def squareLeakCoeffs : Fin 7 → K := ![0,5,-75,350,-700,630,-210]

/-- The sole scalar profile that can leak from the true T8 band at the
terminal-zero fourth-grade square. -/
noncomputable def terminalLeak8 : K[X] := by classical exact ofFn 7 squareLeakCoeffs

omit [CharZero K] in
theorem terminalLeak8_degree : (terminalLeak8 : K[X]).natDegree≤6 := by
  classical
  exact Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)

omit [CharZero K] in
private theorem terminalLeak8_coeff (i : Fin 7) :
    (terminalLeak8 : K[X]).coeff i.val=squareLeakCoeffs i := by
  classical
  exact ofFn_coeff_eq_val_of_lt _ i.isLt

omit [CharZero K] in
theorem terminalLeak8_value (x : K) :
    (terminalLeak8 : K[X]).eval x=5*x-75*x^2+350*x^3-700*x^4+630*x^5-210*x^6 := by
  classical
  unfold terminalLeak8
  rw [ofFn_eq_sum_monomial,eval_finsetSum]
  norm_num [squareLeakCoeffs,Fin.sum_univ_succ]
  ring

omit [CharZero K] in
theorem terminalLeak8_value_zero : (terminalLeak8 : K[X]).eval 0=0 := by
  rw [terminalLeak8_value]
  ring

omit [CharZero K] in
theorem terminalLeak8_value_one : (terminalLeak8 : K[X]).eval 1=0 := by
  rw [terminalLeak8_value]
  ring

private theorem square_leak_probe (ho : HasOrder 12 A b) {k : ℕ} (hk : k<4) :
    probe A b k (evalNodes A terminalLeak8)=0 := by
  have scalar (j : Fin 4) :
      (∑ i : Fin 7, (squareLeakCoeffs i : K)/((j.val+i.val+1:ℕ):K))=0 := by
    fin_cases j <;> norm_num [squareLeakCoeffs,Fin.sum_univ_succ]
  rw [evalNodes_eq_coeffEval A _ terminalLeak8_degree,probe_coeffEval ho (by omega)]
  simp only [terminalLeak8_coeff]
  exact scalar ⟨k,hk⟩

/-- A terminal-zero eighth-grade vector has only one possible polynomial
leak of degree at most six across the paid forward head. -/
theorem grade_eight_single_leak (ha : ∀ i k, i≤k → A i k=0)
    (ho : HasOrder 12 A b) (S : Saturation A b)
    {Z : Submodule K (Fin (s+1) → K)} (split : treeSpace A 8=clockBand6 A⊔Z)
    (terminal : Z≤zeroAt (zeroSpace A 8) (Fin.last s))
    {v : Fin (s+1) → K} (hv : v∈zeroAt (zeroSpace A 8) (Fin.last s)) :
    ∃ α : K, v-α • evalNodes A terminalLeak8∈Z := by
  have h := zeroSpace_le_treeSpace A 8 (mem_zeroAt.mp hv).1
  rw [split] at h
  obtain ⟨y,hy,z,hz,e⟩ := Submodule.mem_sup.mp h
  obtain ⟨P,dp,rfl⟩ := exists_polynomial_of_coeff_range hy
  have hP : evalNodes A P∈zeroAt (zeroSpace A 8) (Fin.last s) := by
    simpa only [←e,add_sub_cancel_right] using
      (zeroAt (zeroSpace A 8) (Fin.last s)).sub_mem hv (terminal hz)
  obtain ⟨pDef,pEnd⟩ := mem_zeroAt.mp hP
  let α := P.coeff 6/(-210:K)
  have lc := terminalLeak8_coeff (K:=K) (6:Fin 7)
  change (terminalLeak8 : K[X]).coeff 6= -210 at lc
  have deg : (P-α • terminalLeak8).natDegree≤5 := by
    have cap := (natDegree_sub_le P (α • terminalLeak8)).trans
      (max_le dp ((natDegree_smul_le ..).trans terminalLeak8_degree))
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rcases (show n=6 ∨ 6<n by omega) with rfl|high
    · rw [coeff_sub,Polynomial.smul_eq_C_mul,Polynomial.coeff_C_mul,lc]
      exact sub_eq_zero.mpr (div_mul_cancel₀ _ (by norm_num : (-210:K)≠0)).symm
    · exact coeff_eq_zero_of_natDegree_lt (cap.trans_lt high)
  have orig : evalNodes A P 0=0 := origin_zeroSpace ha 8 pDef
  have c0 : nodes A 0=0 := by
    simp only [nodes,Matrix.mulVec,dotProduct]
    exact Finset.sum_eq_zero (fun i _ => by rw [ha 0 i (Fin.zero_le i),zero_mul])
  have l0 : evalNodes A terminalLeak8 0=0 := by
    rw [evalNodes_apply,c0,terminalLeak8_value_zero]
  have l1 : evalNodes A terminalLeak8 (Fin.last s)=0 := by
    rw [evalNodes_apply,S.terminalClock,terminalLeak8_value_one]
  have out : P-α • terminalLeak8=0 := by
    apply polynomial_zero_of_endpoint_probes ha ho (n:=4) (by decide) S.terminalClock deg
    · rw [map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,orig,l0,smul_zero,sub_zero]
    · rw [map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,pEnd,l1,smul_zero,sub_zero]
    · intro k hk
      have x : probe A b k (evalNodes A P)=0 := probe_zeroSpace ho (by omega) pDef
      rw [map_sub,map_smul,map_sub,map_smul,x,square_leak_probe ho hk,smul_zero,sub_zero]
  refine ⟨α,?_⟩
  rw [←e,sub_eq_zero.mp out,map_smul,add_sub_cancel_left]
  exact hz

/-- The actual terminal polynomial uses all six allowed degrees. -/
theorem terminalMesh6_natDegree_eq : (terminalMesh6 : K[X]).natDegree=6 := by
  let _ : Infinite K := Infinite.of_injective (fun n : ℕ => (n:K)) Nat.cast_injective
  let P : K[X] := C 132*X^6-C 330*X^5+C 300*X^4-C 120*X^3+C 20*X^2-X
  have eq : terminalMesh6=P := by
    apply Polynomial.funext
    intro x
    rw [terminalMesh6_value]
    simp only [P,eval_sub,eval_add,eval_mul,eval_C,eval_pow,eval_X]
    ring
  have cf : (terminalMesh6 : K[X]).coeff 6=132 := by
    rw [eq]
    norm_num [P,coeff_sub,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X]
  exact le_antisymm terminalMesh6_degree (le_natDegree_of_ne_zero (by rw [cf]; norm_num))

end RKResearch.Certified.Graded.ERK12

