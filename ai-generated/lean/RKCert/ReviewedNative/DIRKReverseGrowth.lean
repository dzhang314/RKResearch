module

public import RKCert.ReviewedNative.DIRKForwardRank
public import RKCert.ReviewedNative.EndpointAdjoint

public section

/-! # Backward strict growth for unrestricted lower triangular tableaux

The all-monomial flag already contains the two weighted reflected seeds at
its second step. Thus after level one, an alleged plateau would contain the
nonzero reflected clock target by the native two-seed theorem. No diagonal
entry is discarded, and the dimension of the first paid seed space is kept.
-/
namespace RKResearch.Certified.Graded.Reverse
open RKResearch Module
open scoped Matrix

variable {K : Type*} [Field K] {s p : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- No plateau from level one onwards; a paid level suffices, even if the
next level is not paid against the chosen forward midpoint. -/
theorem dirk_primitiveBack_lt_succ (ha : A.IsLowerTriangular) (ho : HasOrder p A b)
    {n : ℕ} (hn : 1 ≤ n) (pay : n+2 ≤ p) :
    primitiveBack A b n < primitiveBack A b (n+1) := by
  apply RKCert.ReviewedNative.RankFlags.strict_of_two_seed_forcing
    (N:=mat A.transpose) (D:=diag (reflectedClock A))
    (q₂:=reflectedStageRow A b 1) (q₃:=reflectedStageRow A b 2)
    (target:=diag (reflectedClock A) b)
  · exact adjointFlag_le_succ _ n
  · exact Submodule.map_le_iff_le_comap.mp (adjointFlag_transpose _ n)
  · exact Submodule.map_le_iff_le_comap.mp (adjointFlag_clock _ n)
  · exact adjointFlag_credit _ n (monomial_mem_credit n 1 (by omega))
  · exact adjointFlag_credit _ n (monomial_mem_credit n 2 (by omega))
  · intro h
    have cut := primitiveBack_annih ho 0 n (by omega) h
    exact reflected_target_ne_zero ho (by omega) (mem_annih.mp cut _ (one_mem_treeSpace A 0))
  · exact reverse_dirk_seeds_force_clock ha

/-- The reverse rank at a starting level at least one is carried through
each later paid step, retaining any surplus already earned. -/
theorem dirk_primitiveBack_rank_gain (ha : A.IsLowerTriangular) (ho : HasOrder p A b)
    {r n : ℕ} (hr : 1 ≤ r) (hrn : r ≤ n) (pay : n+1 ≤ p) :
    (n-r)+finrank K (primitiveBack A b r) ≤ finrank K (primitiveBack A b n) :=
  RKCert.ReviewedNative.RankFlags.finrank_gain_of_steps (primitiveBack A b) hrn
    (fun _ h lo => dirk_primitiveBack_lt_succ ha ho (by omega) (by omega))

/-- The first nontrivial paid reverse space contains the actual D(1) and
D(2) rows. Rank zero forces *both* rows to vanish, including at zero weights. -/
theorem dirk_primitiveBack_one_zero
    (h : finrank K (primitiveBack A b 1) = 0) :
    reflectedStageRow A b 0 = 0 ∧ reflectedStageRow A b 1 = 0 := by
  have z := Submodule.finrank_eq_zero.mp h
  have seed (k : ℕ) (hk : k≤1) : reflectedStageRow A b k ∈ primitiveBack A b 1 :=
    adjointFlag_credit _ 0 (monomial_mem_credit 0 k (by omega))
  have f := seed 0 (by decide)
  have g := seed 1 (by decide)
  rw [z, Submodule.mem_bot] at f g
  exact ⟨f,g⟩

/-- At the last live weight, every adjoint seed reads only its original
diagonal entry. No nonzero terminal diagonal is assumed. -/
theorem LastActive.dirk_seed_value {t : Fin s} (L : LastActive b t)
    (ha : A.IsLowerTriangular) (k : ℕ) :
    reflectedStageRow A b k t =
      ((k+1:ℕ):K) * (A t t * (b t * (reflectedClock A t)^k)) -
        b t * (reflectedClock A t)^(k+1) := by
  have m := transpose_mat_pivot ha t (reflectedStageWeight A b k)
    (fun j hj => by simp only [reflectedStageWeight,L.after j hj,zero_mul])
  change ((k+1:ℕ):K) * mat A.transpose (reflectedStageWeight A b k) t -
    reflectedStageWeight A b (k+1) t = _
  rw [m]

/-- The weighted difference D(2) − 2(1−c)D(1), evaluated at the last
live stage, equals b(1−c)². Hence two vanished seeds pin the node to 1. -/
theorem LastActive.dirk_reflected_zero {t : Fin s} (L : LastActive b t)
    (ha : A.IsLowerTriangular) (h₁ : reflectedStageRow A b 0 = 0)
    (h₂ : reflectedStageRow A b 1 = 0) : reflectedClock A t = 0 := by
  have f := L.dirk_seed_value ha 0
  have g := L.dirk_seed_value ha 1
  rw [h₁] at f
  rw [h₂] at g
  simp only [Pi.zero_apply,Nat.reduceAdd,Nat.cast_one,Nat.cast_ofNat,pow_zero,
    pow_one,mul_one,one_mul] at f g
  have e : b t * (reflectedClock A t)^2 = 0 := by
    linear_combination 2 * (reflectedClock A t) * f - g
  exact sq_eq_zero_iff.mp ((mul_eq_zero.mp e).resolve_left L.live)

/-- An arbitrary lower triangular transpose preserves vectors vanishing
on the closed terminal tail (unlike the open-tail improvement for ERK). -/
theorem dirk_transpose_tail {t : Fin s} (ha : A.IsLowerTriangular)
    {v : Fin s → K} (hv : v ∈ tailZero t) : mat A.transpose v ∈ tailZero t := by
  apply mem_tailZero.mpr
  intro i hi
  rw [mat_apply,Matrix.mulVec_apply_eq_sum]
  apply Finset.sum_eq_zero
  intro j _
  by_cases ji : j < i
  · rw [Matrix.transpose_apply,ha ji,zero_mul]
  · rw [mem_tailZero.mp hv j (hi.trans (le_of_not_gt ji)),mul_zero]

theorem LastActive.dirk_primitiveBack_tail {t : Fin s} (L : LastActive b t)
    (ha : A.IsLowerTriangular) (h₁ : reflectedStageRow A b 0 = 0)
    (h₂ : reflectedStageRow A b 1 = 0) (n : ℕ) : primitiveBack A b n ≤ tailZero t := by
  have yt := L.dirk_reflected_zero ha h₁ h₂
  have wt (k : ℕ) : reflectedStageWeight A b (k+1) ∈ tailZero t := by
    apply mem_tailZero.mpr
    intro i hi
    rcases lt_or_eq_of_le hi with lt | rfl
    · simp [reflectedStageWeight,L.after i lt]
    · simp [reflectedStageWeight,yt]
  have seeds (k : ℕ) : reflectedStageRow A b k ∈ tailZero t := by
    cases k with
    | zero => rw [h₁]; exact Submodule.zero_mem _
    | succ k =>
      change ((k+1+1:ℕ):K) • mat A.transpose (reflectedStageWeight A b (k+1)) -
        reflectedStageWeight A b (k+1+1) ∈ tailZero t
      exact (tailZero (K:=K) t).sub_mem ((tailZero (K:=K) t).smul_mem _
        (dirk_transpose_tail ha (wt k))) (wt (k+1))
  induction n with
  | zero =>
    exact (Submodule.span_singleton_le_iff_mem ..).mpr (seeds 0)
  | succ n ih =>
    change _ ⊔ _ ⊔ _ ⊔ _ ≤ _
    refine sup_le (sup_le (sup_le ih ?_) ?_) ?_
    · rintro _ ⟨w,hw,rfl⟩
      exact dirk_transpose_tail ha (ih hw)
    · rintro _ ⟨w,hw,rfl⟩
      exact mem_tailZero.mpr (fun i hi => by rw [diag_apply,mem_tailZero.mp (ih hw) i hi,mul_zero])
    · apply Submodule.span_le.mpr
      rintro _ ⟨k,rfl⟩
      exact seeds k.val

end RKResearch.Certified.Graded.Reverse
