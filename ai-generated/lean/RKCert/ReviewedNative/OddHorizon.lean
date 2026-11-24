module
public import RKCert.ReviewedNative.EndpointAdjoint
public import RKCert.ReviewedNative.GradedGrowth

@[expose] public section

/-! # Saturated odd midpoint on the actual reviewed tableau
The single paid coordinate appears only when the first reverse seed
vanishes. The coordinate is the last *active* output, not a shortened
or reordered tableau.
-/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch Module
noncomputable section
variable {K : Type*} [Field K] {s q p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- The ordinary odd floor, without an order-specific defect surplus. -/
theorem odd_midpoint_floor (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder p A b)
    (q1 : 1 ≤ q) (pay : 2*q+1 ≤ p) : 3*q ≤ s := by
  have small := zeroSpace_finrank ha ho (n:=q-1) (by omega)
  rw [show q-1+1=q by omega] at small
  have dim := treeSpace_rank_eq_of_separation ho (q:=q) (by omega) (coeff_separated ho pay)
  have cnt := backward_endpoint_count ha ho q (q-1) pay (by omega)
  omega

structure OddHorizon (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) (q : ℕ) : Prop where
  flagExact : ∀ n ≤ q-1, finrank K (back A b n) = n + finrank K (back A b 0) ∧
    back A b n = primitiveBack A b n
  firstNonzero : firstSeed A b ≠ 0 → back A b (q-1) = annih (treeSpace A q)
  firstZero : firstSeed A b = 0 → ∃ t : Fin s, LastActive b t ∧
    nodes A t = 1 ∧ coordinate (K:=K) t ∉ treeSpace A q ∧
    back A b (q-1) = zeroAt (annih (treeSpace A q)) t

section Physical
variable {m : ℕ} {T : Matrix (Fin (m+1)) (Fin (m+1)) K} {w : Fin (m+1) → K}

/-- Exact paid reverse ranks when the genuine ordinary midpoint leaves
precisely q dimensions. No assumption on signs, repeated clocks, or the
physical last stage is used. -/
theorem odd_horizon_of_rank (ha : ∀ i j, i ≤ j → T i j = 0) (ho : HasOrder p T w)
    (q1 : 1 ≤ q) (pay : 2*q+1 ≤ p)
    (tight : finrank K (treeSpace T q)+q=m+1) : OddHorizon T w q := by
  let H := q-1
  have hH : H = q-1 := rfl
  let M := annih (treeSpace T q)
  have mm : finrank K M=q := by
    have h := finrank_annih (treeSpace T q)
    rw [Fintype.card_fin] at h
    change finrank K (treeSpace T q)+finrank K M=m+1 at h
    omega
  have hv : primitiveBack T w H ≤ M := primitiveBack_annih ho q H (by dsimp [H]; omega)
  have cut (z : firstSeed T w=0) :
      ∃t : Fin (m+1), LastActive w t ∧ nodes T t=1 ∧
        coordinate (K:=K) t∉treeSpace T q ∧ primitiveBack T w H ≤ zeroAt M t := by
    obtain ⟨t,L⟩ := exists_lastActive ho (by omega)
    have one := L.node_eq_one ha z
    refine ⟨t,L,one,endpoint_coordinate_out ha ho pay t L.live one,?_⟩
    intro v vH
    exact mem_zeroAt.mpr ⟨hv vH,mem_tailZero.mp (L.primitiveBack_tail ha z H vH) t le_rfl⟩
  have lim : finrank K (primitiveBack T w H) ≤ H+finrank K (back T w 0) := by
    by_cases z : firstSeed T w=0
    · obtain ⟨t,_,_,out,inc⟩ := cut z
      have e : finrank K (zeroAt M t)+1=finrank K M :=
        finrank_zeroAt_annih _ t out
      have le := Submodule.finrank_mono inc
      rw [first_dim_zero z,add_zero]
      omega
    · have le := Submodule.finrank_mono hv
      rw [first_dim_one z]
      omega
  have flags (n : ℕ) (hn : n ≤ H) :
      finrank K (back T w n)=n+finrank K (back T w 0) ∧
        back T w n=primitiveBack T w n := by
    have g := primitiveBack_interval ha ho n (H-n) (by dsimp [H] at *;omega)
    rw [show n+(H-n)=H by omega] at g
    have low := back_finrank ha ho n (by dsimp [H] at *; omega)
    have inc := back_le_primitiveBack (A:=T) (b:=w) n
    have h := Submodule.finrank_mono inc
    exact ⟨by omega,Submodule.eq_of_le_of_finrank_le inc (by omega)⟩
  have hf : back T w H=primitiveBack T w H := (flags H le_rfl).2
  refine ⟨flags,?_,?_⟩
  · intro z
    have a := (flags H le_rfl).1
    rw [first_dim_one z] at a
    have inc : back T w H ≤ M := hf.symm ▸ hv
    change back T w H = M
    exact Submodule.eq_of_le_of_finrank_le inc (by omega)
  · intro z
    obtain ⟨t,L,one,out,inc⟩ := cut z
    refine ⟨t,L,one,out,?_⟩
    change back T w H = zeroAt M t
    apply Submodule.eq_of_le_of_finrank_le (show back T w H ≤ zeroAt M t from hf.symm ▸ inc)
    have e : finrank K (zeroAt M t)+1=finrank K M :=
      finrank_zeroAt_annih _ t out
    have a := (flags H le_rfl).1
    rw [first_dim_zero z,add_zero] at a
    omega

end Physical
end
end RKResearch.Certified.Graded.Reverse
