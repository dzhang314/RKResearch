module

public import RKCert.ReviewedNative.FiniteClockMomentLadder
public import RKCert.ReviewedNative.HiddenClockLeakage
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! The finite ladder on the actual weighted columns. The mixed paid test
comes from `HasOrder p A b`, and the chronological endpoints are the
existing strict ERK and lower-triangular DIRK leakage endpoints. -/

namespace RKResearch

open Polynomial RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteClockMoments
open scoped BigOperators Matrix Classical

noncomputable section

variable {ι K : Type*} [Fintype ι] [Field K]

namespace ClockLeakage

/-- Grouped physical clocks, not stages carrying individual output. -/
def physicalClocks (A : Matrix ι ι K) : Finset K := Finset.univ.image (clock A)

theorem clock_mem_physicalClocks (A : Matrix ι ι K) (i : ι) :
    clock A i ∈ physicalClocks A :=
  Finset.mem_image_of_mem (clock A) (Finset.mem_univ i)

theorem groupedColumn_zero_off_physicalClocks (A : Matrix ι ι K) (b : ι → K)
    {x : K} (off : x ∉ physicalClocks A) (F : K[X]) : groupedColumn A b x F = 0 := by
  rw [groupedColumn_eq_columns]
  apply Finset.sum_eq_zero
  intro i hi
  have h := clock_mem_physicalClocks A i
  rw [mem_fibre.mp hi] at h
  exact (off h).elim

/-- Any finite certificate for the *net* nonzero off-visible grouped columns. -/
structure HiddenClockCover (A : Matrix ι ι K) (b : ι → K)
    (T : Finset K) (F : K[X]) (H : Finset K) : Prop where
  offVisible : ∀ x ∈ H, x ∉ T
  zeroOutside : ∀ x, x ∉ T → x ∉ H → groupedColumn A b x F = 0

/-- The exact effective support; repeated clocks are already summed. -/
def effectiveHiddenClocks (A : Matrix ι ι K) (b : ι → K) (T : Finset K)
    (F : K[X]) : Finset K :=
  ((physicalClocks A) \ T).filter (fun x => groupedColumn A b x F ≠ 0)

theorem effectiveHiddenClocks_cover (A : Matrix ι ι K) (b : ι → K)
    (T : Finset K) (F : K[X]) : HiddenClockCover A b T F (effectiveHiddenClocks A b T F) := by
  constructor
  · intro x hx
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).2
  · intro x off outside
    by_cases phys : x ∈ physicalClocks A
    · by_cases zero : groupedColumn A b x F = 0
      · exact zero
      · exact (outside
          (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨phys, off⟩, zero⟩)).elim
    · exact groupedColumn_zero_off_physicalClocks A b phys F

private theorem clockValues_decompose (A : Matrix ι ι K) (C : Finset K)
    (maps : ∀ i, clock A i ∈ C) (f : K → K) :
    (fun i => f (clock A i)) = ∑ x ∈ C, f x • stopMask A x := by
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, stopMask]
  calc
    f (clock A i) = f (clock A i) * (if clock A i = clock A i then 1 else 0) := by
      simp only [ite_true, mul_one]
    _ = _ := by
      symm
      apply Finset.sum_eq_single_of_mem (clock A i) (maps i)
      intro x _ ne
      rw [if_neg ne.symm, mul_zero]

private theorem rowFunctional_group (A : Matrix ι ι K) (b : ι → K) (F : K[X])
    (C : Finset K) (maps : ∀ i, clock A i ∈ C) (f : K → K) :
    rowFunctional A b F (fun i => f (clock A i)) =
      ∑ x ∈ C, f x * groupedColumn A b x F := by
  rw [clockValues_decompose A C maps f, map_sum]
  simp only [map_smul, smul_eq_mul, groupedColumn]

private theorem output_group (A : Matrix ι ι K) (b : ι → K)
    (C : Finset K) (maps : ∀ i, clock A i ∈ C) (f : K → K) :
    (∑ i, b i * f (clock A i)) = ∑ x ∈ C, outputMass A b x * f x := by
  calc
    _ = ∑ x ∈ C, ∑ i ∈ fibre A x, b i * f (clock A i) := by
      simpa only [fibre] using
        (Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := C) (g := clock A)
          (fun i _ => maps i) (fun i => b i * f (clock A i))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [outputMass, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [mem_fibre.mp hi]

/-- Structural zero of the hidden grouped columns gives actual zero
of the existing weighted leakage functional, for any source selector. -/
theorem hiddenLeakage_zero_of_offVisible_columns (A : Matrix ι ι K) (b : ι → K)
    (T : Finset K) (Q F : K[X]) (zero : ∀ x, x ∉ T → groupedColumn A b x F = 0) :
    hiddenLeakage A b T Q F = 0 := by
  let f : K → K := fun x => if x ∈ T then 0 else Q.eval x
  change rowFunctional A b F (fun i => f (clock A i)) = 0
  rw [rowFunctional_group A b F (physicalClocks A) (clock_mem_physicalClocks A) f]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : x ∈ T
  · simp only [f, if_pos hx, zero_mul]
  · rw [zero x hx, mul_zero]

variable [CharZero K]

/-- Compare an actual full grouped column to its paid quadrature value. -/
def suffixDefect (A : Matrix ι ι K) (b : ι → K) (F : K[X]) (x : K) : K :=
  outputMass A b x * integral x 1 F - groupedColumn A b x F

private theorem degree_reflect_le (F : K[X]) : (F.comp (1 - X)).natDegree ≤ F.natDegree := by
  have one : (1 - X : K[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
  exact natDegree_comp_le.trans
    (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left F.natDegree one)

end ClockLeakage

open ClockLeakage

namespace HasOrder

variable [CharZero K] {A : Matrix ι ι K} {b : ι → K} {p : ℕ}

/-- The coalesced mixed identity, for every paid source test, not just
for a selector vanishing at all other visible clocks. -/
theorem hiddenClock_momentLaw (ho : HasOrder p A b) {T H : Finset K} (F : K[X])
    (cover : ∀ x, x ∉ T → outputMass A b x = 0)
    (hidden : HiddenClockCover A b T F H) (Q : K[X])
    (paid : Q.natDegree + F.natDegree + 2 ≤ p) :
    moment H (fun x => groupedColumn A b x F) Q = moment T (suffixDefect A b F) Q := by
  let W := H ∪ (physicalClocks A \ T)
  let C := T ∪ W
  let ρ := fun x => groupedColumn A b x F
  let E := fun x => outputMass A b x * integral x 1 F
  have off : ∀ x ∈ W, x ∉ T := by
    intro x h
    rcases Finset.mem_union.mp h with hH | hR
    · exact hidden.offVisible x hH
    · exact (Finset.mem_sdiff.mp hR).2
  have apart : Disjoint T W := by
    apply Finset.disjoint_left.mpr
    intro x hxT hxW
    exact off x hxW hxT
  have maps : ∀ i, clock A i ∈ C := by
    intro i
    by_cases hi : clock A i ∈ T
    · exact Finset.mem_union.mpr (Or.inl hi)
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr
        (Finset.mem_sdiff.mpr ⟨clock_mem_physicalClocks A i, hi⟩))))
  have full : moment C ρ Q = moment C E Q := by
    calc
      _ = rowFunctional A b F (fun i => Q.eval (clock A i)) := by
        rw [ClockLeakage.rowFunctional_group A b F C maps (fun x => Q.eval x), moment_apply]
        apply Finset.sum_congr rfl
        intro x _
        exact mul_comm _ _
      _ = ∑ i, b i * (Q.eval (clock A i) * integral (clock A i) 1 F) :=
        paid_rowFunctional_test ho Q F paid
      _ = _ := by
        rw [ClockLeakage.output_group A b C maps (fun x => Q.eval x * integral x 1 F), moment_apply]
        apply Finset.sum_congr rfl
        intro x _
        dsimp only [E]
        ac_rfl
  have split (mass : K → K) : moment C mass Q = moment T mass Q + moment W mass Q := by
    simp only [C, moment_apply, Finset.sum_union apart]
  have tail : moment H ρ Q = moment W ρ Q := by
    simp only [moment_apply]
    apply Finset.sum_subset (fun _ hx => Finset.mem_union.mpr (Or.inl hx))
    intro x hx outside
    have zero : ρ x = 0 := hidden.zeroOutside x (off x hx) outside
    rw [zero, zero_mul]
  have exactOff : moment W E Q = 0 := by
    rw [moment_apply]
    apply Finset.sum_eq_zero
    intro x hx
    simp only [E, cover x (off x hx), zero_mul]
  rw [split ρ, split E, ← tail, exactOff, add_zero] at full
  change moment H ρ Q = _
  calc
    _ = moment T E Q - moment T ρ Q := eq_sub_of_add_eq ((add_comm _ _).trans full)
    _ = _ := by simp only [moment_apply, suffixDefect, E, ρ, sub_mul, Finset.sum_sub_distrib]

/-- The exact source-test budget `p-d-2` and the simultaneous finite
ladder with `p-d-T.card-1 + S.card` monomial tests. -/
theorem hiddenClock_ladder_iff (ho : HasOrder p A b) {T S H : Finset K} {d : ℕ}
    (nonempty : T.Nonempty) (sub : S ⊆ T) (F : K[X]) (degree : F.natDegree ≤ d)
    (budget : d + T.card + 1 ≤ p)
    (cover : ∀ x, x ∉ T → outputMass A b x = 0)
    (hidden : HiddenClockCover A b T F H) :
    (∀ a ∈ S, groupedColumn A b a F = outputMass A b a * integral a 1 F) ↔
      TiltedTests H (T \ S) (fun x => groupedColumn A b x F) (p - d - T.card - 1 + S.card) := by
  have positive : 0 < T.card := Finset.card_pos.mpr nonempty
  have base : T.card ≤ (p - d - 2) + 1 := by omega
  have count : paidCount T S (p - d - 2) = p - d - T.card - 1 + S.card := by
    rw [paidCount_eq_add sub base]
    omega
  have law (Q : K[X]) (hQ : Q.natDegree ≤ p - d - 2) :
      moment H (fun x => groupedColumn A b x F) Q = moment T (suffixDefect A b F) Q :=
    ho.hiddenClock_momentLaw F cover hidden Q (by omega)
  have eq : (∀ a ∈ S, groupedColumn A b a F = outputMass A b a * integral a 1 F) ↔
      (∀ a ∈ S, suffixDefect A b F a = 0) := by
    constructor
    · intro good a ha
      exact sub_eq_zero.mpr (good a ha).symm
    · intro good a ha
      have hz : outputMass A b a * integral a 1 F - groupedColumn A b a F = 0 := good a ha
      exact (sub_eq_zero.mp hz).symm
  exact eq.trans (by
    simpa only [count] using zero_on_stops_iff_tilted_tests
      (H := H) (fun x => groupedColumn A b x F) (suffixDefect A b F) sub base law)

/-- Low support turns the moment ladder into literal zero off-visible
columns. With `S = ∅` the certified-stop premises are vacuous. -/
theorem hiddenClock_zero_of_low_support (ho : HasOrder p A b) {T S H : Finset K} {d : ℕ}
    (nonempty : T.Nonempty) (sub : S ⊆ T) (F : K[X]) (degree : F.natDegree ≤ d)
    (budget : d + T.card + 1 ≤ p)
    (cover : ∀ x, x ∉ T → outputMass A b x = 0)
    (hidden : HiddenClockCover A b T F H)
    (good : ∀ a ∈ S, groupedColumn A b a F = outputMass A b a * integral a 1 F)
    (size : H.card ≤ p - d - T.card - 1 + S.card) :
    ∀ x, x ∉ T → groupedColumn A b x F = 0 := by
  have tests := (ho.hiddenClock_ladder_iff nonempty sub F degree budget cover hidden).mp good
  have off : ∀ x ∈ H, x ∉ T \ S := by
    intro x h he
    exact hidden.offVisible x h (Finset.mem_sdiff.mp he).1
  have zero := mass_zero_of_tilted_tests (fun x => groupedColumn A b x F) off size tests
  intro x hx
  by_cases h : x ∈ H
  · exact zero x h
  · exact hidden.zeroOutside x hx h

/-- The reflected physical profile is charged once, without changing the
actual source-clock cover or counting any extra diagonal term. -/
theorem hiddenLeakage_reflected_zero_of_effective_support (ho : HasOrder p A b)
    {T S : Finset K} {a : K} {d : ℕ} (ha : a ∈ T) (sub : S ⊆ T)
    (F : K[X]) (degree : F.natDegree ≤ d) (budget : d + T.card + 1 ≤ p)
    (cover : ∀ x, x ∉ T → outputMass A b x = 0)
    (good : ∀ t ∈ S, groupedColumn A b t (F.comp (1 - X)) =
      outputMass A b t * integral t 1 (F.comp (1 - X)))
    (size : (effectiveHiddenClocks A b T (F.comp (1 - X))).card ≤
      p - d - T.card - 1 + S.card) :
    hiddenLeakage A b T (visibleSelector T a) (F.comp (1 - X)) = 0 := by
  let P := F.comp (1 - X)
  have degreeP : P.natDegree ≤ d := (ClockLeakage.degree_reflect_le F).trans degree
  have zero := ho.hiddenClock_zero_of_low_support ⟨a, ha⟩ sub P degreeP budget cover
    (effectiveHiddenClocks_cover A b T P) good size
  exact hiddenLeakage_zero_of_offVisible_columns A b T (visibleSelector T a) P zero

variable [LinearOrder ι]

/-- Actual ERK client. Structural support erases leakage, not the strict
weighted column: that separate physical cancellation is still required. -/
theorem erk_reflected_local_zero_of_hidden_ladder (ho : HasOrder p A b)
    (strict : ∀ i j, i ≤ j → A i j = 0)
    {T S : Finset K} {a : K} {d : ℕ} (ha : a ∈ T) (sub : S ⊆ T)
    (F : K[X]) (degree : F.natDegree ≤ d) (budget : d + T.card + 1 ≤ p)
    (cover : ∀ x, x ∉ T → outputMass A b x = 0) (live : outputMass A b a ≠ 0)
    (good : ∀ t ∈ S, groupedColumn A b t (F.comp (1 - X)) =
      outputMass A b t * integral t 1 (F.comp (1 - X)))
    (size : (effectiveHiddenClocks A b T (F.comp (1 - X))).card ≤
      p - d - T.card - 1 + S.card)
    (strictZero : strictColumn A b a (F.comp (1 - X)) = 0) : integral 0 (1 - a) F = 0 :=
  ho.erk_visibleClock_reflected_local_zero strict ha F cover (by omega) live strictZero
    (ho.hiddenLeakage_reflected_zero_of_effective_support ha sub F degree budget cover good size)

/-- Actual DIRK client. The true root removes the diagonal term, not
an independent signed stop atom. No common or positive diagonal is needed. -/
theorem dirk_reflected_local_zero_of_hidden_ladder (ho : HasOrder p A b)
    (lower : A.IsLowerTriangular)
    {T S : Finset K} {a : K} {d : ℕ} (ha : a ∈ T) (sub : S ⊆ T)
    (F : K[X]) (degree : F.natDegree ≤ d) (budget : d + T.card + 1 ≤ p)
    (cover : ∀ x, x ∉ T → outputMass A b x = 0) (live : outputMass A b a ≠ 0)
    (good : ∀ t ∈ S, groupedColumn A b t (F.comp (1 - X)) =
      outputMass A b t * integral t 1 (F.comp (1 - X)))
    (size : (effectiveHiddenClocks A b T (F.comp (1 - X))).card ≤
      p - d - T.card - 1 + S.card)
    (stopRoot : F.eval (1 - a) = 0) (strictZero : strictColumn A b a (F.comp (1 - X)) = 0) :
    integral 0 (1 - a) F = 0 :=
  ho.dirk_visibleClock_reflected_local_zero lower ha F cover (by omega) live stopRoot strictZero
    (ho.hiddenLeakage_reflected_zero_of_effective_support ha sub F degree budget cover good size)

end HasOrder
end
end RKResearch
