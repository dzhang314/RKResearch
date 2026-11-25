module

public import RKCert.ReviewedNative.AffineReceiverPrefix

@[expose] public section

/-! # Inclusive native affine prefix for lower triangular arrays -/
namespace RKResearch.Certified.Graded

open RKResearch FiniteRootedTree
open scoped BigOperators Matrix FiniteRootedTree
noncomputable section

variable {K : Type*} [Field K] {s k : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {l : Fin s→K}
variable {x : K} {cut : Fin s}

/-- A strictly-above-diagonal zero is enough for this prefix identity. -/
theorem prefix_mulVec_of_lower (lower : ∀ i j,i<j→A i j=0)
    (hk : k≤s) (v : Fin s→K) :
    prefixMatrix A hk *ᵥ prefixRestrict hk v=prefixRestrict hk (A *ᵥ v) := by
  ext i
  exact sum_prefix_zero_tail hk (fun j=>A (Fin.castLE hk i) j*v j)
    (fun j hj=>by rw [lower _ _ (by change i.val<j.val; have h := i.isLt; omega),zero_mul])

theorem Φ_prefix_of_lower (lower : ∀ i j,i<j→A i j=0) (hk : k≤s)
    (T : FiniteRootedTree) :
    Φ T (prefixMatrix A hk)=prefixRestrict hk (Φ T A) := by
  induction T with
  | leaf => rfl
  | butcherProduct t b ihT ihB =>
    rw [Φ,Φ,ihT,ihB,prefix_mulVec_of_lower lower hk]
    rfl

/-- Lower triangularity preserves the last possible donor; its literal
coefficient is exactly the last probe coefficient times the diagonal. -/
theorem ClockAffineProbe.row_at_cut_of_lower (P : ClockAffineProbe A l x cut)
    (lower : ∀ i j,i<j→A i j=0) :
    affineReceiverRow A l cut=l cut*A cut cut := by
  unfold affineReceiverRow
  refine Finset.sum_eq_single cut ?_ ?_
  · intro i _ ne
    rcases lt_or_gt_of_ne ne with early | late
    · rw [lower i cut early,mul_zero]
    · rw [P.afterCut i late,zero_mul]
  · intro notMem
    exact (notMem (Finset.mem_univ _)).elim

theorem ClockAffineProbe.row_after_cut_of_lower (P : ClockAffineProbe A l x cut)
    (lower : ∀ i j,i<j→A i j=0) (j : Fin s) (past : cut<j) :
    affineReceiverRow A l j=0 := by
  unfold affineReceiverRow
  apply Finset.sum_eq_zero
  intro i _
  by_cases later : cut<i
  · rw [P.afterCut i later,zero_mul]
  · rw [lower i j ((le_of_not_gt later).trans_lt past),mul_zero]

/-- The receiver may use any original prefix on which its actual
combined row is supported. Both matrix and output row are divided
by the nonzero common clock. -/
theorem ClockAffineProbe.prefix_hasOrder_of_lower_tail
    (P : ClockAffineProbe A l x cut) (lower : ∀ i j,i<j→A i j=0)
    (hk : k≤s) (tail : ∀ j : Fin s,k≤j.val→affineReceiverRow A l j=0)
    (nz : x≠0) (q : ℕ) (paid : ∀ v∈zeroSpace A q, row l v=0) :
    HasOrder q (x⁻¹ • prefixMatrix A hk)
      (fun j : Fin k=>x⁻¹*affineReceiverRow A l (Fin.castLE hk j)) := by
  intro T hT
  let r := x⁻¹
  let B := prefixMatrix A hk
  let b₀ : Fin k→K := fun j=>r*affineReceiverRow A l (Fin.castLE hk j)
  have hz := paid _ (zeroSpace_mono A hT (rootStageResidual_mem A T))
  change row l ((T.factorial:K) • (A *ᵥ Φ T A) -
      (fun i=>(nodes A i)^(T.order:ℕ)))=0 at hz
  rw [map_sub,map_smul,smul_eq_mul,P.power_pairing,sub_eq_zero] at hz
  have z : (T.factorial:K)*(affineReceiverRow A l ⬝ᵥ Φ T A)=x^(T.order:ℕ) := by
    simpa only [row_apply,affineReceiverRow_pairing] using hz
  have scal : r*r^((T.order:ℕ)-1)=r^(T.order:ℕ) := by
    rw [←pow_succ']
    congr 1
    have hp := T.order.pos
    omega
  have mass : b₀ ⬝ᵥ Φ T (r•B)=r^(T.order:ℕ)*(affineReceiverRow A l ⬝ᵥ Φ T A) := by
    unfold B
    rw [Φ_smul,Φ_prefix_of_lower lower hk,dotProduct]
    simp only [b₀,Pi.smul_apply,smul_eq_mul,prefixRestrict_apply]
    have term (j : Fin k) :
        r*affineReceiverRow A l (Fin.castLE hk j) *
          (r^((T.order:ℕ)-1)*Φ T A (Fin.castLE hk j)) =
        r^(T.order:ℕ)*(affineReceiverRow A l (Fin.castLE hk j) *
          Φ T A (Fin.castLE hk j)) := by
      rw [←scal]
      ac_rfl
    rw [Finset.sum_congr rfl (fun j _=>term j),←Finset.mul_sum]
    rw [sum_prefix_zero_tail hk (fun j=>affineReceiverRow A l j*Φ T A j)
      (fun j hj=>by rw [tail j hj,zero_mul])]
    rfl
  change (T.factorial:K)*(b₀ ⬝ᵥ Φ T (r•B))=1
  rw [mass,mul_left_comm,z,←mul_pow]
  simp [r,nz]

theorem ClockAffineProbe.prefix_hasOrder_inclusive_of_lower
    (P : ClockAffineProbe A l x cut) (lower : ∀ i j,i<j→A i j=0)
    (nz : x≠0) (q : ℕ) (paid : ∀ v∈zeroSpace A q, row l v=0) :
    HasOrder q (x⁻¹ • prefixMatrix A (Nat.succ_le_of_lt cut.isLt))
      (fun j : Fin (cut.val+1)=>x⁻¹*affineReceiverRow A l
        (Fin.castLE (Nat.succ_le_of_lt cut.isLt) j)) := by
  apply P.prefix_hasOrder_of_lower_tail lower (Nat.succ_le_of_lt cut.isLt) _ nz q paid
  intro j past
  exact P.row_after_cut_of_lower lower j (show cut<j from past)

/-- The old strict cut still works if the one literal self coefficient
vanishes, regardless of the other diagonal entries. -/
theorem ClockAffineProbe.prefix_hasOrder_exclusive_of_lower_of_self_zero
    (P : ClockAffineProbe A l x cut) (lower : ∀ i j,i<j→A i j=0)
    (selfZero : l cut*A cut cut=0)
    (nz : x≠0) (q : ℕ) (paid : ∀ v∈zeroSpace A q, row l v=0) :
    HasOrder q (x⁻¹ • prefixMatrix A cut.isLt.le)
      (fun j : Fin cut.val=>x⁻¹*affineReceiverRow A l (Fin.castLE cut.isLt.le j)) := by
  apply P.prefix_hasOrder_of_lower_tail lower cut.isLt.le _ nz q paid
  intro j past
  have cj : cut≤j := past
  rcases eq_or_lt_of_le cj with same | later
  · rw [←same,P.row_at_cut_of_lower lower,selfZero]
  · exact P.row_after_cut_of_lower lower j later

theorem scaled_prefix_lower (lower : ∀ i j,i<j→A i j=0) (hk : k≤s) (a : K) :
    ∀ i j : Fin k,i<j→(a • prefixMatrix A hk) i j=0 := by
  intro i j ij
  change a*A (Fin.castLE hk i) (Fin.castLE hk j)=0
  rw [lower _ _ (show Fin.castLE hk i<Fin.castLE hk j from ij),mul_zero]

theorem scaled_prefix_constant_diagonal (hk : k≤s) {γ : K} (a : K)
    (eq : ∀ i,A i i=γ) (i : Fin k) :
    (a • prefixMatrix A hk) i i=a*γ := by
  change a*A (Fin.castLE hk i) (Fin.castLE hk i)=_
  rw [eq]

end
end RKResearch.Certified.Graded
