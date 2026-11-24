module
public import RKCert.ReviewedNative.ReverseFlag
public import RKCert.ReviewedNative.EndpointCauchy

@[expose] public section

/-! # Exact last-live-coordinate refund in the native reverse budget -/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch Module
open scoped Matrix
noncomputable section

variable {K : Type*} [Field K] {s p : ℕ}

structure LastActive (b : Fin s → K) (t : Fin s) : Prop where
  live : b t ≠ 0
  after : ∀ i, t < i → b i=0

variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

theorem exists_lastActive (ho : HasOrder A b p) (hp : 1 ≤ p) :
    ∃t : Fin s,LastActive b t := by
  classical
  let U : Finset (Fin s) := Finset.univ.filter (fun i=>b i ≠ 0)
  have ne : U.Nonempty := by
    by_contra no
    have z : b=0 := by
      funext i
      change b i = 0
      by_contra ni
      exact no ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ni⟩⟩
    have h:=ho.bushy_moment 0 hp
    simp [z,stageMass,dotProduct] at h
  let t:=U.max' ne
  refine ⟨t,⟨(Finset.mem_filter.mp (U.max'_mem ne)).2,?_⟩⟩
  intro i lt
  by_contra ni
  have m : i∈U:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,ni⟩
  exact (not_le_of_gt lt) (U.le_max' i m)

theorem transpose_tail_zero (ha : ∀ i j,i ≤ j → A i j=0) {t : Fin s}
    {v : Fin s → K} (h : ∀ j : Fin s, t < j → v j = 0) {i : Fin s}
    (ht : t ≤ i) : mat A.transpose v i = 0 := by
  simp only [mat_apply,Matrix.mulVec,dotProduct,Matrix.transpose_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_cases je : j ≤ i
  · rw [ha j i je,zero_mul]
  · rw [h j (lt_of_le_of_lt ht (lt_of_not_ge je)),mul_zero]

theorem LastActive.reflected_zero {t : Fin s}(L : LastActive b t)
    (ha : ∀ i j,i ≤ j → A i j=0)(first : firstSeed A b=0) :
    reflectedClock A t=0 := by
  have b0 : reflectedStageWeight A b 0=b := by
    funext i
    simp [reflectedStageWeight]
  have m : (A.transpose *ᵥ b) t=0 := transpose_tail_zero ha L.after (i:=t) le_rfl
  have h := congrFun first t
  change reflectedStageRow A b 0 t=0 at h
  rw [reflectedStageRow,b0] at h
  simp only [Nat.zero_add,Nat.cast_one,one_smul,Pi.sub_apply,reflectedStageWeight,pow_one,
    m,zero_sub,neg_eq_zero] at h
  exact (mul_eq_zero.mp h).resolve_left L.live

theorem LastActive.node_eq_one {t : Fin s}(L : LastActive b t)
    (ha : ∀ i j,i ≤ j → A i j=0)(first : firstSeed A b=0) :
    nodes A t=1 := by
  exact (sub_eq_zero.mp (L.reflected_zero ha first)).symm

def tailZero (t : Fin s) : Submodule K (Fin s → K) :=
  ⨅ i : {j : Fin s // t ≤ j}, LinearMap.ker (LinearMap.proj i.val)

theorem mem_tailZero {t : Fin s} {v : Fin s → K} :
    v∈tailZero t ↔ ∀ i, t ≤ i → v i=0 := by
  simp [tailZero,Submodule.mem_iInf,LinearMap.mem_ker,Subtype.forall]

theorem LastActive.seed_tail {t : Fin s} (L : LastActive b t)
    (ha : ∀ i j,i ≤ j → A i j=0) (first : firstSeed A b=0) (k : ℕ) :
    reflectedStageRow A b k∈tailZero t := by
  apply mem_tailZero.mpr
  intro i it
  have w : ∀ j, t < j → reflectedStageWeight A b k j=0 := by
    intro j jh
    simp [reflectedStageWeight,L.after j jh]
  have m : (A.transpose *ᵥ reflectedStageWeight A b k) i=0 :=
    transpose_tail_zero ha w it
  have e : reflectedStageWeight A b (k+1) i=0 := by
    by_cases h : i = t
    · subst i
      have yi:=L.reflected_zero ha first
      simp [reflectedStageWeight,yi,pow_succ]
    · exact by simp [reflectedStageWeight,L.after i (lt_of_le_of_ne it (Ne.symm h))]
  simp only [reflectedStageRow,Pi.sub_apply,Pi.smul_apply,m,e,smul_zero,sub_zero]

theorem adjointFlag_tail {t : Fin s} (ha : ∀ i j,i ≤ j → A i j=0)
    (first : firstSeed A b=0) (C : ℕ → Submodule K (Fin s → K))
    (paid : ∀n,C n ≤ tailZero t) (n : ℕ) :
    adjointFlag A b C n ≤ tailZero t := by
  induction n with
  | zero =>
    change K∙firstSeed A b ≤ _
    rw [first,Submodule.span_singleton_eq_bot.mpr rfl]
    exact bot_le
  | succ n ih =>
    change _⊔_⊔_⊔_ ≤ _
    refine sup_le (sup_le (sup_le ih ?_) ?_) (paid n)
    · rintro _ ⟨v,hv,rfl⟩
      apply mem_tailZero.mpr
      intro i ti
      exact transpose_tail_zero ha (fun _ h=>mem_tailZero.mp (ih hv) _ h.le) ti
    · rintro _ ⟨v,hv,rfl⟩
      apply mem_tailZero.mpr
      intro i ti
      rw [diag_apply,mem_tailZero.mp (ih hv) i ti,mul_zero]

theorem LastActive.back_tail {t : Fin s} (L : LastActive b t)
    (ha : ∀ i j,i ≤ j → A i j=0) (first : firstSeed A b=0) (n : ℕ) :
    back A b n ≤ tailZero t :=
  adjointFlag_tail ha first _ (fun _=>(Submodule.span_singleton_le_iff_mem ..).mpr
    (L.seed_tail ha first 1)) n

theorem LastActive.primitiveBack_tail {t : Fin s} (L : LastActive b t)
    (ha : ∀ i j,i ≤ j → A i j=0) (first : firstSeed A b=0) (n : ℕ) :
    primitiveBack A b n ≤ tailZero t := by
  apply adjointFlag_tail ha first
    (monomialCredit A b) _ n
  intro j
  apply Submodule.span_le.mpr
  rintro _ ⟨k,rfl⟩
  exact L.seed_tail ha first k.val

theorem first_dim_zero (first : firstSeed A b=0) : finrank K (back A b 0)=0 := by
  change finrank K (K∙firstSeed A b)=0
  rw [first,Submodule.span_singleton_eq_bot.mpr rfl,finrank_bot]

theorem first_dim_one (first : firstSeed A b ≠ 0) : finrank K (back A b 0)=1 :=
  finrank_span_singleton first

private theorem backward_endpoint_count_succ {m : ℕ} {T : Matrix (Fin (m+1)) (Fin (m+1)) K}
    {w : Fin (m+1) → K}
    (ha : ∀i j,i ≤ j → T i j=0) (ho : HasOrder T w p)
    (q n : ℕ) (oq : 2*q+1 ≤ p) (budget : q+n+2 ≤ p) :
    finrank K (treeSpace T q)+n+1 ≤ m+1 := by
  by_cases z : firstSeed T w=0
  · obtain ⟨t,L⟩:=exists_lastActive ho (by omega)
    have out := endpoint_coordinate_out ha ho oq t L.live (L.node_eq_one ha z)
    have inc : back T w n ≤ zeroAt (annih (treeSpace T q)) t := by
      intro v hv
      exact mem_zeroAt.mpr ⟨back_annih ho q n budget hv,
        mem_tailZero.mp (L.back_tail ha z n hv) t le_rfl⟩
    have a:=Submodule.finrank_mono inc
    have b:=finrank_zeroAt_annih (treeSpace T q) t out
    have c:=finrank_annih (treeSpace T q)
    have d:=back_finrank ha ho n (by omega)
    rw [first_dim_zero z,zero_add] at d
    rw [Fintype.card_fin] at c
    omega
  · have h:=backward_count ha ho q n budget
    rw [first_dim_one z] at h
    omega

/-- The last-live coordinate or the nonzero linear seed, but never both,
pays one physical dimension in the lower-bound count. -/
theorem backward_endpoint_count (ha : ∀i j,i ≤ j → A i j=0) (ho : HasOrder A b p)
    (q n : ℕ) (oq : 2*q+1 ≤ p) (budget : q+n+2 ≤ p) :
    finrank K (treeSpace A q)+n+1 ≤ s := by
  cases s with
  | zero =>
    obtain ⟨t,_⟩:=exists_lastActive ho (by omega)
    exact Fin.elim0 t
  | succ m =>
    exact backward_endpoint_count_succ ha ho q n oq budget

/-- Paid forward room for the actual order-nine explicit tableau. -/
theorem orderNine_paid_room (ha : ∀i j,i ≤ j → A i j=0) (ho : HasOrder A b 9) :
    finrank K (treeSpace A 4)+4 ≤ s :=
  backward_endpoint_count ha ho 4 3 (by decide) (by decide)

end
end RKResearch.Certified.Graded.Reverse
