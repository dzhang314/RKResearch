module

public import RKCert.ReviewedNative.ClockBlockDetection

@[expose] public section

/-! # Inclusive (diagonal-retaining) native Hermite rank gains
The sample lift is simultaneous on every row through and including the
last detecting row.  Including this row costs one clock degree compared
with a strictly triangular tableau. All defects below are native. -/
namespace RKResearch.Certified.Graded

open Polynomial RKCert.Endpoint Module
open scoped Matrix Classical

variable {K : Type*} [Field K] [CharZero K] {s p j : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

private theorem derivative_native_primitive (P : K[X]) : (primitive P).derivative = P := by
  ext k
  rw [coeff_derivative,primitive_coeff_succ]
  simpa only [Nat.cast_add,Nat.cast_one] using
    div_mul_cancel₀ (P.coeff k) (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k) : ((k+1:ℕ):K)≠0)

/-- An inclusive sample sees the last selected knot as a double root
as well. Divisibility and the degree count hold over a nonordered field. -/
private theorem inclusive_primitive_detect (S : Finset K) (Q : K[X])
    (d : Q.natDegree+1 < S.card)
    (zero : ∀ z∈S, (primitive (nodalHull S * Q)).IsRoot z) : Q=0 := by
  let F := primitive (nodalHull S * Q)
  have deriv : F.derivative = nodalHull S * Q := derivative_native_primitive _
  by_contra nz
  have fnz : F≠0 := by
    intro fz
    rw [fz,map_zero] at deriv
    exact (mul_ne_zero (monic_nodalHull S).ne_zero nz) deriv.symm
  have sq (z : K) (hz : z∈S) : (X-C z)^2 ∣ F := by
    apply (le_rootMultiplicity_iff fnz).mp
    apply (one_lt_rootMultiplicity_iff_isRoot fnz).mpr
    exact ⟨zero z hz, by rw [deriv]; simp [IsRoot,nodalHull_eval_of_mem hz]⟩
  have div : nodalHull S ^ 2 ∣ F := by
    rw [nodalHull,← Finset.prod_pow]
    exact Finset.prod_dvd_of_coprime (fun a _ b _ hn =>
      (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hn).isUnit).pow) sq
  apply fnz (eq_zero_of_dvd_of_natDegree_lt div ?_)
  have deg := primitive_natDegree_le (natDegree_mul_le (p:=nodalHull S) (q:=Q))
  change F.natDegree ≤ _ at deg
  rw [natDegree_pow,natDegree_nodalHull]
  rw [natDegree_nodalHull] at deg
  omega

/-- The detecting maps are built on the same actual tableau. The input
and its lift agree through the last selected row, so the diagonal is
retained; no hypothesis about diagonal entries is made. -/
theorem dirk_inclusive_hermite_family (ha : A.IsLowerTriangular)
    (U : Submodule K (Fin s → K)) (mask : MaskInvariant (nodes A) U)
    {r : ℕ} (pos : 0<r) (count : r≤(failedNodes (nodes A) 1 U s).card) :
    ∃ L D : (Fin r → K) →ₗ[K] (Fin s → K),
      (∀ q, L q∈U) ∧
      (∀ q, ∃ P : K[X], P.natDegree≤2*r ∧
        D q = evalNodes A (primitive P) - mat A (evalNodes A P) + mat A (L q)) ∧
      (∀ q, D q∈U → q=0) := by
  classical
  let c := nodes A
  obtain ⟨k,hs,hnew,hk⟩ := exists_rth_failure c 1 U pos count
  let B := failedNodes c 1 U (k.val+1)
  let S := insert 0 B
  have hB : B=insert (c k) (failedNodes c 1 U k.val) := by
    apply Finset.Subset.antisymm (failedNodes_step c 1 U k)
    intro a ha'
    rcases Finset.mem_insert.mp ha' with rfl | hm
    · exact hk
    · exact failedNodes_mono c 1 U (Nat.le_succ _) hm
  have h0 : 0 ∉ B := fun hz => (mem_failedNodes.mp hz).1 rfl
  have size : S.card=r+1 := by
    rw [show S=insert 0 B from rfl,Finset.card_insert_of_notMem h0,hB,Finset.card_insert_of_notMem hnew,hs]
  let H := nodalHull S
  obtain ⟨w,hw,matchW⟩ := exists_masked_prefix_lift c 1 mask (k.val+1) H
    (nodalHull_eval_of_mem (Finset.mem_insert_self _ _))
    (fun a ha' => nodalHull_eval_of_mem (Finset.mem_insert_of_mem ha'))
  let L := (weightedEval c w).comp (ofFn r)
  let G := ((evalNodes A).comp primitive - (mat A).comp (evalNodes A)).comp
    ((LinearMap.mulLeft K H).comp (ofFn r))
  let D := G + (mat A).comp L
  have eqL (q : Fin r → K) : L q = weightedEval c w (ofFn r q) := rfl
  have eqD (q : Fin r → K) : D q =
      evalNodes A (primitive (H*ofFn r q)) - mat A (evalNodes A (H*ofFn r q)) +
      mat A (L q) := rfl
  refine ⟨L,D,?_,?_,?_⟩
  · intro q
    have he : L q = fun i => (ofFn r q).eval (c i)*w i := by ext i; simp [eqL]
    rw [he]
    exact mulByBlock_mem c mask (fun a => (ofFn r q).eval a) hw
  · intro q
    have dq := ofFn_natDegree_lt pos q
    have dh : H.natDegree = S.card := natDegree_nodalHull S
    refine ⟨H*ofFn r q,(natDegree_mul_le).trans (by omega),eqD q⟩
  · intro q hqu
    let Q := ofFn r q
    let F := primitive (H*Q)
    have agree (i : Fin s) (hi : i.val<k.val+1) : D q i = F.eval (c i) := by
      have e : mat A (evalNodes A (H*Q)) i = mat A (L q) i := by
        rw [mat_apply,mat_apply,Matrix.mulVec_apply_eq_sum,Matrix.mulVec_apply_eq_sum]
        apply Finset.sum_congr rfl
        intro l _
        by_cases hl : l ≤ i
        · congr 1
          rw [evalNodes_apply,eqL,weightedEval_apply,matchW l (by change l.val ≤ i.val at hl; omega),eval_mul]
          simp only [Pi.one_apply,mul_one,c,Q]
          ac_rfl
        · rw [ha (lt_of_not_ge hl),zero_mul,zero_mul]
      rw [eqD]
      change F.eval (c i) - mat A (evalNodes A (H*Q)) i + mat A (L q) i = _
      rw [e,sub_add_cancel]
    have z (a : K) (ha' : a∈B) : F.IsRoot a := by
      change F.eval a = 0
      by_contra nz
      apply (mem_failedNodes.mp ha').2
      refine ⟨(F.eval a)⁻¹ • D q,U.smul_mem _ hqu,?_⟩
      intro i hi hci
      change (F.eval a)⁻¹*D q i=1
      rw [agree i hi,hci,inv_mul_cancel₀ nz]
    apply injective_ofFn r
    rw [map_zero]
    apply inclusive_primitive_detect S Q
    · have h := ofFn_natDegree_lt pos q
      dsimp [Q]
      omega
    · intro a ha'
      rcases Finset.mem_insert.mp ha' with rfl | ha'
      · change (primitive (H * Q)).eval 0 = 0
        rw [← coeff_zero_eq_eval_zero,primitive_coeff_zero]
      · exact z a ha'

/-- A clock-invariant subspace of genuine F_j costs j/2 *extra* dimensions
in F_(j+1). The space need not be invariant under the tableau itself. -/
theorem dirk_forward_invariant_outgoing (ha : A.IsLowerTriangular)
    (ho : HasOrder A b p) (pay : j+1≤p) (U : Submodule K (Fin s → K))
    (hUF : U≤zeroSpace A j) (inv : ∀ v∈U, diag (nodes A) v∈U) :
    finrank K U + j/2 ≤ finrank K (zeroSpace A (j+1)) := by
  have mono := hUF.trans (zeroSpace_mono A (Nat.le_succ _))
  by_cases zero : j/2=0
  · simpa [zero] using Submodule.finrank_mono mono
  have mask := clock_mask_invariant inv
  have count := paid_failed_clock_blocks ho pay hUF mask (r:=j/2) (by omega)
  obtain ⟨L,D,hL,hD,sep⟩ := dirk_inclusive_hermite_family ha U mask (Nat.pos_of_ne_zero zero) count
  apply finrank_add_of_independent_mod mono D _ sep
  intro q
  obtain ⟨P,hp,hd⟩ := hD q
  rw [hd]
  apply (zeroSpace A (j+1)).add_mem _ (mat_zeroSpace ho j pay (hUF (hL q)))
  simpa only [neg_sub] using (zeroSpace A (j+1)).neg_mem (primitive_defect A P (by omega : P.natDegree≤j))

/-- If it is the *higher* space F_(j+1) that is clock-invariant, the
same physical sample pays j/2 dimensions from F_j into F_(j+1). -/
theorem dirk_forward_invariant_incoming (ha : A.IsLowerTriangular)
    (ho : HasOrder A b p) (pay : j+2≤p)
    (inv : ∀ v∈zeroSpace A (j+1), diag (nodes A) v∈zeroSpace A (j+1)) :
    finrank K (zeroSpace A j) + j/2 ≤ finrank K (zeroSpace A (j+1)) := by
  let U := zeroSpace A (j+1)
  have mono := zeroSpace_mono A (Nat.le_succ j)
  by_cases zero : j/2=0
  · simpa [zero] using Submodule.finrank_mono mono
  have mask := clock_mask_invariant inv
  have count := paid_failed_clock_blocks ho (j:=j+1) (by omega) (le_refl U) mask (r:=j/2) (by omega)
  obtain ⟨L,D,hL,hD,sep⟩ := dirk_inclusive_hermite_family ha U mask (Nat.pos_of_ne_zero zero) count
  apply finrank_add_of_independent_mod mono L hL
  intro q hq
  apply sep
  obtain ⟨P,hp,hd⟩ := hD q
  rw [hd]
  apply U.add_mem _ (mat_zeroSpace ho j (by omega) hq)
  simpa only [neg_sub] using U.neg_mem (primitive_defect A P (by omega : P.natDegree≤j))

end RKResearch.Certified.Graded
