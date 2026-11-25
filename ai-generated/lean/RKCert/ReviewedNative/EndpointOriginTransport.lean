module

public import RKCert.ReviewedNative.EndpointAdjoint

@[expose] public section

/-! # Transport of a last-active reflected origin

The local transport only needs strict chronology and a last-active weight.
It does not need the global first seed to vanish or any rooted-tree payment.
Actual payment can provide inclusion in an annihilator; saturation then
identifies the endpoint coordinate without any change of tableau.
-/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch
open scoped Matrix

noncomputable section

variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- On the actual last-active tail only the diagonal term of a reflected
seed can remain. -/
theorem LastActive.reflectedStageRow_at_or_after {t i : Fin s} (last : LastActive b t)
    (ha : ∀ i j, i ≤ j → A i j = 0) (k : ℕ) (hi : t ≤ i) :
    reflectedStageRow A b k i = -reflectedStageWeight A b (k+1) i := by
  have zero (j : Fin s) (hj : t < j) : reflectedStageWeight A b k j = 0 := by
    simp [reflectedStageWeight,last.after j hj]
  have hz : (A.transpose *ᵥ reflectedStageWeight A b k) i = 0 :=
    transpose_tail_zero ha zero hi
  simp only [reflectedStageRow,Pi.sub_apply,Pi.smul_apply,hz,smul_zero,zero_sub]

theorem LastActive.firstSeed_at_last {t : Fin s} (last : LastActive b t)
    (ha : ∀ i j, i ≤ j → A i j = 0) :
    firstSeed A b t = -(b t * reflectedClock A t) := by
  change reflectedStageRow A b 0 t = _
  simpa only [reflectedStageWeight,Nat.zero_add,pow_one] using
    last.reflectedStageRow_at_or_after ha 0 (i:=t) le_rfl

/-- The origin tests the single marked entry, not the entire first seed. -/
theorem LastActive.reflected_zero_iff_firstSeed_at_last {t : Fin s}
    (last : LastActive b t) (ha : ∀ i j, i ≤ j → A i j = 0) :
    reflectedClock A t = 0 ↔ firstSeed A b t = 0 := by
  rw [last.firstSeed_at_last ha,neg_eq_zero,mul_eq_zero]
  exact ⟨Or.inr,fun hz => hz.resolve_left last.live⟩

theorem LastActive.reflectedStageRow_tail_of_origin {t : Fin s} (last : LastActive b t)
    (ha : ∀ i j, i ≤ j → A i j = 0) (origin : reflectedClock A t = 0) (k : ℕ) :
    reflectedStageRow A b k ∈ tailZero t := by
  apply mem_tailZero.mpr
  intro i hi
  rw [last.reflectedStageRow_at_or_after ha k hi]
  by_cases he : i = t
  · subst i
    simp [reflectedStageWeight,origin,pow_succ]
  · simp [reflectedStageWeight,last.after i (lt_of_le_of_ne hi (Ne.symm he))]

private theorem firstSeed_mem_adjointFlag (C : ℕ → Submodule K (Fin s → K)) (n : ℕ) :
    firstSeed A b ∈ adjointFlag A b C n := by
  have hz : firstSeed A b ∈ adjointFlag A b C 0 :=
    Submodule.mem_span_singleton_self _
  have mono : Monotone (adjointFlag A b C) :=
    monotone_nat_of_le_succ (adjointFlag_le_succ (A:=A) (b:=b) C)
  exact mono (Nat.zero_le n) hz

/-- Only the credits used through the given grade need to have the
original tail-zero property. The first seed is allowed to be nonzero. -/
theorem adjointFlag_le_tailZero_of_firstSeed_mem (ha : ∀ i j, i ≤ j → A i j = 0)
    (C : ℕ → Submodule K (Fin s → K)) {t : Fin s} (first : firstSeed A b ∈ tailZero t)
    (n : ℕ) (credit : ∀ k < n, C k ≤ tailZero t) :
    adjointFlag A b C n ≤ tailZero t := by
  revert credit
  induction n with
  | zero =>
    intro _
    change K ∙ firstSeed A b ≤ tailZero t
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr first
  | succ n ih =>
    intro credit
    have inc := ih (fun k hk => credit k (lt_trans hk (Nat.lt_succ_self n)))
    change _ ⊔ _ ⊔ _ ⊔ _ ≤ tailZero t
    refine sup_le (sup_le (sup_le inc ?_) ?_) (credit n (Nat.lt_succ_self n))
    · rintro _ ⟨v,hv,rfl⟩
      apply mem_tailZero.mpr
      intro i hi
      exact transpose_tail_zero ha (fun _ h => mem_tailZero.mp (inc hv) _ h.le) hi
    · rintro _ ⟨v,hv,rfl⟩
      apply mem_tailZero.mpr
      intro i hi
      rw [diag_apply,mem_tailZero.mp (inc hv) i hi,mul_zero]

/-- For an arbitrary actual credit sequence, the converse needs only the
first seed in the flag. The forward direction needs the displayed finite
tail condition on the credits. -/
theorem LastActive.reflected_zero_iff_adjointFlag_vanishes {t : Fin s} (last : LastActive b t)
    (ha : ∀ i j, i ≤ j → A i j = 0) (C : ℕ → Submodule K (Fin s → K)) (n : ℕ)
    (credit : ∀ k < n, reflectedClock A t = 0 → C k ≤ tailZero t) :
    reflectedClock A t = 0 ↔ ∀ w ∈ adjointFlag A b C n, w t = 0 := by
  constructor
  · intro origin w hw
    have inc := adjointFlag_le_tailZero_of_firstSeed_mem ha C
      (last.reflectedStageRow_tail_of_origin ha origin 0) n (fun k hk => credit k hk origin)
    exact mem_tailZero.mp (inc hw) t le_rfl
  · intro vanish
    exact (last.reflected_zero_iff_firstSeed_at_last ha).mpr
      (vanish _ (firstSeed_mem_adjointFlag (A:=A) (b:=b) C n))

theorem LastActive.reflected_zero_iff_back_vanishes {t : Fin s} (last : LastActive b t)
    (ha : ∀ i j, i ≤ j → A i j = 0) (n : ℕ) :
    reflectedClock A t = 0 ↔ ∀ w ∈ back A b n, w t = 0 :=
  last.reflected_zero_iff_adjointFlag_vanishes ha (pairCredit A b) n
    (fun _ _ origin => (Submodule.span_singleton_le_iff_mem _ _).mpr
      (last.reflectedStageRow_tail_of_origin ha origin 1))

theorem LastActive.reflected_zero_iff_primitiveBack_vanishes {t : Fin s}
    (last : LastActive b t) (ha : ∀ i j, i ≤ j → A i j = 0) (n : ℕ) :
    reflectedClock A t = 0 ↔ ∀ w ∈ primitiveBack A b n, w t = 0 := by
  apply last.reflected_zero_iff_adjointFlag_vanishes ha (monomialCredit A b) n
  intro k _ origin
  apply Submodule.span_le.mpr
  rintro _ ⟨m,rfl⟩
  exact last.reflectedStageRow_tail_of_origin ha origin m.val

/-- Pure marked-coordinate duality; independent of chronology or order. -/
theorem coordinate_mem_iff_annih_vanishes_at {ι : Type*} [Fintype ι]
    (V : Submodule K (ι → K)) (t : ι) :
    coordinate (K:=K) t ∈ V ↔ ∀ w ∈ annih V, w t = 0 := by
  constructor
  · intro ht w hw
    simpa only [row_coordinate] using mem_annih.mp hw _ ht
  · intro vanish
    rw [←annih_annih V]
    apply mem_annih.mpr
    intro w hw
    rw [row_apply,dotProduct_comm,←row_apply,row_coordinate]
    exact vanish w hw

/-- Inclusion in a paid annihilator already gives this direction. It
does not use any condition on the higher credits. -/
theorem LastActive.reflected_zero_of_coordinate_mem_of_adjointFlag_le_annih {t : Fin s}
    (last : LastActive b t) (ha : ∀ i j, i ≤ j → A i j = 0)
    (C : ℕ → Submodule K (Fin s → K)) (n : ℕ) (V : Submodule K (Fin s → K))
    (inc : adjointFlag A b C n ≤ annih V) (ht : coordinate (K:=K) t ∈ V) :
    reflectedClock A t = 0 :=
  (last.reflected_zero_iff_firstSeed_at_last ha).mpr
    ((coordinate_mem_iff_annih_vanishes_at V t).mp ht _
      (inc (firstSeed_mem_adjointFlag (A:=A) (b:=b) C n)))

/-- Under exact saturation, the pointwise origin test is precisely
membership of the physical endpoint column in the forward space. -/
theorem LastActive.reflected_zero_iff_coordinate_mem_of_adjointFlag_eq_annih {t : Fin s}
    (last : LastActive b t) (ha : ∀ i j, i ≤ j → A i j = 0)
    (C : ℕ → Submodule K (Fin s → K)) (n : ℕ) (V : Submodule K (Fin s → K))
    (credit : ∀ k < n, reflectedClock A t = 0 → C k ≤ tailZero t)
    (sat : adjointFlag A b C n = annih V) :
    reflectedClock A t = 0 ↔ coordinate (K:=K) t ∈ V := by
  rw [coordinate_mem_iff_annih_vanishes_at V t,←sat]
  exact last.reflected_zero_iff_adjointFlag_vanishes ha C n credit

theorem LastActive.reflected_zero_iff_coordinate_mem_of_back_eq_annih {t : Fin s}
    (last : LastActive b t) (ha : ∀ i j, i ≤ j → A i j = 0)
    (n : ℕ) (V : Submodule K (Fin s → K)) (sat : back A b n = annih V) :
    reflectedClock A t = 0 ↔ coordinate (K:=K) t ∈ V := by
  rw [coordinate_mem_iff_annih_vanishes_at V t,←sat]
  exact last.reflected_zero_iff_back_vanishes ha n

theorem LastActive.reflected_zero_iff_coordinate_mem_of_primitiveBack_eq_annih {t : Fin s}
    (last : LastActive b t) (ha : ∀ i j, i ≤ j → A i j = 0)
    (n : ℕ) (V : Submodule K (Fin s → K)) (sat : primitiveBack A b n = annih V) :
    reflectedClock A t = 0 ↔ coordinate (K:=K) t ∈ V := by
  rw [coordinate_mem_iff_annih_vanishes_at V t,←sat]
  exact last.reflected_zero_iff_primitiveBack_vanishes ha n

/-- A literal rooted-tree annihilation payment gives the one-way test
without assuming that any reverse flag has saturated. -/
theorem LastActive.reflected_zero_of_coordinate_mem_treeSpace {t : Fin s}
    (last : LastActive b t) (ha : ∀ i j, i ≤ j → A i j = 0)
    {p : ℕ} (ho : HasOrder p A b) (j : ℕ) (pay : j+2 ≤ p)
    (ht : coordinate (K:=K) t ∈ treeSpace A j) :
    reflectedClock A t = 0 := by
  have paid : firstSeed A b ∈ annih (treeSpace A j) :=
    reflectedStageRow_annih ho j 0 (by simpa only [Nat.add_zero] using pay)
  exact (last.reflected_zero_iff_firstSeed_at_last ha).mpr
    ((coordinate_mem_iff_annih_vanishes_at (treeSpace A j) t).mp ht _ paid)

end

end RKResearch.Certified.Graded.Reverse
