module

public import RKCert.ReviewedNative.ClockSuffixRowFunctional
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The affine hidden-clock row functional at a visible stop

A selector erases other *grouped output* clocks. It need not erase
the incoming weighted columns at zero-output clocks. The latter
contribution is the value of a literal linear row functional.

This file has no signed-law or atom conclusion. -/

namespace RKResearch

open Polynomial
open RKCert.Endpoint RKCert.ReviewedNative.PositiveRule19
open scoped BigOperators Matrix Classical

noncomputable section

variable {ι K : Type*} [Fintype ι] [Field K]

namespace ClockLeakage

def fibre (A : Matrix ι ι K) (t : K) : Finset ι :=
  Finset.univ.filter (fun i => clock A i = t)

@[simp] theorem mem_fibre {A : Matrix ι ι K} {t : K} {i : ι} :
    i ∈ fibre A t ↔ clock A i = t := by
  simp [fibre]

/-- Total output on a physical clock, allowing signed cancellation. -/
def outputMass (A : Matrix ι ι K) (b : ι → K) (t : K) : K :=
  ∑ i ∈ fibre A t, b i

def stopMask (A : Matrix ι ι K) (t : K) (i : ι) : K :=
  if clock A i = t then 1 else 0

/-- The same paid selector restricted to physical stages whose clock
is outside the aggregate output cover. No individual output is used. -/
def hiddenMask (A : Matrix ι ι K) (T : Finset K) (Q : K[X]) (i : ι) : K :=
  if clock A i ∈ T then 0 else Q.eval (clock A i)

def visibleSelector (T : Finset K) (t : K) : K[X] :=
  nodalHull (T.erase t)

theorem visibleSelector_ne (T : Finset K) (t : K) : (visibleSelector T t).eval t ≠ 0 := by
  rw [visibleSelector, nodalHull, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro x hx
  simp only [eval_sub, eval_X, eval_C]
  exact sub_ne_zero.mpr (Finset.mem_erase.mp hx).1.symm

private theorem visibleSelector_off {T : Finset K} {t x : K} (hx : x ∈ T) (ne : x ≠ t) :
    (visibleSelector T t).eval x = 0 := by
  simpa only [visibleSelector] using
    (nodalHull_eval_of_mem (Finset.mem_erase.mpr ⟨ne, hx⟩))

/-- The full grouped physical weighted column, including diagonal. -/
def groupedColumn (A : Matrix ι ι K) (b : ι → K) (t : K) (F : K[X]) : K :=
  rowFunctional A b F (stopMask A t)

/-- The unisolated part of the mixed test, as an actual row functional. -/
def hiddenLeakage (A : Matrix ι ι K) (b : ι → K) (T : Finset K) (Q F : K[X]) : K :=
  rowFunctional A b F (hiddenMask A T Q)

/-- A sufficient physical support condition, tested at the weighted
receiver rows. The hidden target stages' own output weights are
irrelevant. The main identity also admits cancellations weaker than this. -/
theorem hiddenLeakage_eq_zero_of_tested_rows (A : Matrix ι ι K) (b : ι → K)
    (T : Finset K) (Q F : K[X])
    (kill : ∀ j, b j * F.eval (clock A j) ≠ 0 → (A *ᵥ hiddenMask A T Q) j = 0) :
    hiddenLeakage A b T Q F = 0 := by
  rw [hiddenLeakage, rowFunctional_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_cases h : b j * F.eval (clock A j) = 0
  · rw [h, zero_mul]
  · rw [kill j h, mul_zero]

private theorem split_clock_values (A : Matrix ι ι K) {T : Finset K} {t : K}
    (ht : t ∈ T) (Q : K[X]) (off : ∀ x ∈ T, x ≠ t → Q.eval x = 0) :
    (fun i => Q.eval (clock A i)) =
      Q.eval t • stopMask A t + hiddenMask A T Q := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, stopMask, hiddenMask]
  by_cases hit : clock A i = t
  · simp only [hit, ite_true, ite_eq_left ht, mul_one, add_zero]
  · by_cases inside : clock A i ∈ T
    · simp only [if_neg hit, if_pos inside, mul_zero, add_zero, off _ inside hit]
    · simp only [if_neg hit, if_neg inside, mul_zero, zero_add]

private theorem sum_after_visible_selector (A : Matrix ι ι K) (b : ι → K)
    {T : Finset K} {t : K} (Q : K[X]) (g : K → K)
    (cover : ∀ x, x ∉ T → outputMass A b x = 0)
    (off : ∀ x ∈ T, x ≠ t → Q.eval x = 0) :
    (∑ i, b i * (Q.eval (clock A i) * g (clock A i))) =
      (Q.eval t * outputMass A b t) * g t := by
  let S := insert t (Finset.univ.image (clock A))
  let f : K → K := fun x => Q.eval x * g x
  have maps (i : ι) (_ : i ∈ Finset.univ) : clock A i ∈ S :=
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem (clock A) (Finset.mem_univ i))
  change (∑ i, b i * f (clock A i)) = _
  calc
    _ = ∑ x ∈ S, ∑ i ∈ fibre A x, b i * f (clock A i) := by
      simpa only [fibre] using
        (Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := S) (g := clock A)
          maps (fun i => b i * f (clock A i))).symm
    _ = ∑ x ∈ S, outputMass A b x * f x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [outputMass, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [mem_fibre.mp hi]
    _ = outputMass A b t * f t := by
      apply Finset.sum_eq_single_of_mem t (Finset.mem_insert_self _ _)
      intro x _ hxt
      by_cases live : x ∈ T
      · simp only [f, off x live hxt, zero_mul, mul_zero]
      · rw [cover x live, zero_mul]
    _ = _ := by dsimp only [f]; ring

/-- Expand the weighted receiver row back to actual physical columns.
The sum over stages at the stop does not test their own output weights. -/
theorem groupedColumn_eq_columns (A : Matrix ι ι K) (b : ι → K) (t : K) (F : K[X]) :
    groupedColumn A b t F =
      ∑ i ∈ fibre A t, ∑ j, b j * A j i * F.eval (clock A j) := by
  have mask (j : ι) : (A *ᵥ stopMask A t) j = ∑ i ∈ fibre A t, A j i := by
    simp only [Matrix.mulVec_apply_eq_sum, fibre, Finset.sum_filter, stopMask,
      mul_ite, mul_one, mul_zero]
  rw [groupedColumn, rowFunctional_apply]
  calc
    _ = ∑ j, ∑ i ∈ fibre A t, b j * F.eval (clock A j) * A j i := by
      simp only [mask, Finset.mul_sum]
    _ = ∑ i ∈ fibre A t, ∑ j, b j * F.eval (clock A j) * A j i := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

section Chronological

variable [LinearOrder ι]

def strictColumn (A : Matrix ι ι K) (b : ι → K) (t : K) (F : K[X]) : K :=
  ∑ i ∈ fibre A t, ∑ j ∈ Finset.univ.filter (fun j => i < j),
    b j * A j i * F.eval (clock A j)

def diagonalMass (A : Matrix ι ι K) (b : ι → K) (t : K) : K :=
  ∑ i ∈ fibre A t, b i * A i i

private theorem chronological_sum (i : ι) (f : ι → K)
    (zero : ∀ j, j < i → f j = 0) :
    (∑ j, f j) = (∑ j ∈ Finset.univ.filter (fun j => i < j), f j) + f i := by
  let S := Finset.univ.filter (fun j => i < j)
  have sub : S ⊆ Finset.univ.erase i := by
    intro j hj
    have ij : i < j := (Finset.mem_filter.mp hj).2
    exact Finset.mem_erase.mpr ⟨ne_of_gt ij, Finset.mem_univ j⟩
  have replace : (∑ j ∈ S, f j) = ∑ j ∈ Finset.univ.erase i, f j := by
    apply Finset.sum_subset sub
    intro j hj notin
    have ji : j ≠ i := (Finset.mem_erase.mp hj).1
    have notAfter : ¬ i < j :=
      fun ij => notin (Finset.mem_filter.mpr ⟨Finset.mem_univ j, ij⟩)
    exact zero j (lt_of_le_of_ne (le_of_not_gt notAfter) ji)
  change (∑ j, f j) = (∑ j ∈ S, f j) + f i
  rw [replace, Finset.sum_erase_add _ _ (Finset.mem_univ i)]

/-- Chronological consumers split off the exact diagonal term rather
than reading the grouped weight as an individual output. -/
theorem groupedColumn_eq_strict_diagonal {A : Matrix ι ι K} (ha : A.IsLowerTriangular)
    (b : ι → K) (t : K) (F : K[X]) :
    groupedColumn A b t F = strictColumn A b t F + diagonalMass A b t * F.eval t := by
  rw [groupedColumn_eq_columns]
  calc
    _ = ∑ i ∈ fibre A t,
        ((∑ j ∈ Finset.univ.filter (fun j => i < j), b j * A j i * F.eval (clock A j)) +
          b i * A i i * F.eval t) := by
      apply Finset.sum_congr rfl
      intro i hi
      have before (j : ι) (hj : j < i) : b j * A j i * F.eval (clock A j) = 0 := by
        rw [@ha j i hj, mul_zero, zero_mul]
      rw [chronological_sum i (fun j => b j * A j i * F.eval (clock A j)) before,
        mem_fibre.mp hi]
    _ = _ := by
      simp only [strictColumn, diagonalMass, Finset.sum_add_distrib, Finset.sum_mul]

end Chronological
end ClockLeakage

open ClockLeakage

namespace HasOrder

variable [CharZero K] {A : Matrix ι ι K} {b : ι → K} {p : ℕ}

/-- The exact affine identity for any polynomial that selects the
aggregate output fibre. A separate physical row-functional value
accounts for the entire off-cover part. -/
theorem clockColumn_hiddenLeakage_affine (ho : HasOrder p A b)
    {T : Finset K} {t : K} (ht : t ∈ T) (Q F : K[X])
    (cover : ∀ x, x ∉ T → outputMass A b x = 0)
    (off : ∀ x ∈ T, x ≠ t → Q.eval x = 0)
    (paid : Q.natDegree + F.natDegree + 2 ≤ p) :
    (Q.eval t * outputMass A b t) * integral t 1 F =
      Q.eval t * groupedColumn A b t F + hiddenLeakage A b T Q F := by
  calc
    _ = ∑ i, b i * (Q.eval (clock A i) * integral (clock A i) 1 F) :=
      (ClockLeakage.sum_after_visible_selector A b Q (fun x => integral x 1 F) cover off).symm
    _ = rowFunctional A b F (fun i => Q.eval (clock A i)) :=
      (paid_rowFunctional_test ho Q F paid).symm
    _ = _ := by
      simp only [ClockLeakage.split_clock_values A ht Q off, map_add, map_smul, smul_eq_mul,
        groupedColumn, hiddenLeakage]

/-- Charge only the finite aggregate output cover, not all physical
stages. The hidden part remains in the equation and is not free zero. -/
theorem visibleClock_hiddenLeakage_affine (ho : HasOrder p A b)
    {T : Finset K} {t : K} (ht : t ∈ T) (F : K[X])
    (cover : ∀ x, x ∉ T → outputMass A b x = 0)
    (paid : F.natDegree + T.card + 1 ≤ p) :
    ((visibleSelector T t).eval t * outputMass A b t) * integral t 1 F =
      (visibleSelector T t).eval t * groupedColumn A b t F +
        hiddenLeakage A b T (visibleSelector T t) F := by
  have cost : (visibleSelector T t).natDegree + F.natDegree + 2 ≤ p := by
    rw [visibleSelector, natDegree_nodalHull, Finset.card_erase_of_mem ht]
    have nonempty : 0 < T.card := Finset.card_pos.mpr ⟨t, ht⟩
    omega
  exact ho.clockColumn_hiddenLeakage_affine ht (visibleSelector T t) F cover
    (fun _ hx ne => ClockLeakage.visibleSelector_off hx ne) cost

private theorem reflect_degree (F : K[X]) : (F.comp (1 - X)).natDegree ≤ F.natDegree := by
  have d : (1 - X : K[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
  exact natDegree_comp_le.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left F.natDegree d)

private theorem reflected_integral (F : K[X]) (t : K) :
    integral t 1 (F.comp (1 - X)) = integral 0 (1 - t) F := by
  have twice : (F.comp (1 - X)).comp (1 - X) = F := by
    rw [comp_assoc, show ((1 - X : K[X]).comp (1 - X)) = X by
      simp only [sub_comp, one_comp, X_comp, sub_sub_cancel], comp_X]
  have edge : integral t 1 (F.comp (1 - X)) =
      integral 0 (1 - t) ((F.comp (1 - X)).comp (1 - X)) :=
    (integral_reflect (F.comp (1 - X)) t).symm
  exact edge.trans (congrArg (fun P : K[X] => integral 0 (1 - t) P) twice)

/-- Analytic left-stop form of the same physical suffix identity.
Only the profile is pulled back in the row functional. The selector
and aggregate output cover stay at the actual physical clocks. -/
theorem visibleClock_reflected_hiddenLeakage_affine (ho : HasOrder p A b)
    {T : Finset K} {t : K} (ht : t ∈ T) (F : K[X])
    (cover : ∀ x, x ∉ T → outputMass A b x = 0)
    (paid : F.natDegree + T.card + 1 ≤ p) :
    ((visibleSelector T t).eval t * outputMass A b t) * integral 0 (1 - t) F =
      (visibleSelector T t).eval t * groupedColumn A b t (F.comp (1 - X)) +
        hiddenLeakage A b T (visibleSelector T t) (F.comp (1 - X)) := by
  have d := reflect_degree F
  have physical := ho.visibleClock_hiddenLeakage_affine ht (F.comp (1 - X)) cover (by omega)
  exact (congrArg
    (fun v : K => ((visibleSelector T t).eval t * outputMass A b t) * v)
    (reflected_integral F t).symm).trans physical

/-- The same affine law after cancelling the nonzero finite selector.
This divides by no output weight and no diagonal. -/
theorem visibleClock_reflected_hiddenLeakage_eq (ho : HasOrder p A b)
    {T : Finset K} {t : K} (ht : t ∈ T) (F : K[X])
    (cover : ∀ x, x ∉ T → outputMass A b x = 0)
    (paid : F.natDegree + T.card + 1 ≤ p) :
    outputMass A b t * integral 0 (1 - t) F =
      groupedColumn A b t (F.comp (1 - X)) +
        hiddenLeakage A b T (visibleSelector T t) (F.comp (1 - X)) /
          (visibleSelector T t).eval t := by
  let q := (visibleSelector T t).eval t
  let B := outputMass A b t
  let I := integral 0 (1 - t) F
  let N := groupedColumn A b t (F.comp (1 - X))
  let L := hiddenLeakage A b T (visibleSelector T t) (F.comp (1 - X))
  have h : (q * B) * I = q * N + L :=
    ho.visibleClock_reflected_hiddenLeakage_affine ht F cover paid
  have live : q ≠ 0 := visibleSelector_ne T t
  have diff : B * I - N = L / q := by
    apply (eq_div_iff live).mpr
    calc
      _ = (q * B) * I - q * N := by ring
      _ = _ := by rw [h]; ring
  change B * I = N + L / q
  calc
    _ = (B * I - N) + N := by ring
    _ = _ := by rw [diff]; ring

/-- The precise total cancellation criterion. The two summands on the
right may compensate; neither stop erasure nor separate cancellation
is asserted. -/
theorem visibleClock_reflected_zero_iff (ho : HasOrder p A b)
    {T : Finset K} {t : K} (ht : t ∈ T) (F : K[X])
    (cover : ∀ x, x ∉ T → outputMass A b x = 0)
    (paid : F.natDegree + T.card + 1 ≤ p) (live : outputMass A b t ≠ 0) :
    integral 0 (1 - t) F = 0 ↔
      (visibleSelector T t).eval t * groupedColumn A b t (F.comp (1 - X)) +
        hiddenLeakage A b T (visibleSelector T t) (F.comp (1 - X)) = 0 := by
  have eq := ho.visibleClock_reflected_hiddenLeakage_affine ht F cover paid
  constructor
  · intro z
    simpa only [z, mul_zero] using eq.symm
  · intro z
    rw [z] at eq
    exact (mul_eq_zero.mp eq).resolve_left (mul_ne_zero (visibleSelector_ne T t) live)

variable [LinearOrder ι]

/-- Strict ERK client: the diagonal is zero by the actual strict
tableau hypothesis, so no stop root is required on the source side. -/
theorem erk_visibleClock_reflected_local_zero (ho : HasOrder p A b)
    (strict : ∀ i j, i ≤ j → A i j = 0)
    {T : Finset K} {t : K} (ht : t ∈ T) (F : K[X])
    (cover : ∀ x, x ∉ T → outputMass A b x = 0)
    (paid : F.natDegree + T.card + 1 ≤ p) (live : outputMass A b t ≠ 0)
    (strictZero : strictColumn A b t (F.comp (1 - X)) = 0)
    (leakZero : hiddenLeakage A b T (visibleSelector T t) (F.comp (1 - X)) = 0) :
    integral 0 (1 - t) F = 0 := by
  have lower : A.IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    exact strict i j (le_of_lt hij)
  have diagZero : diagonalMass A b t = 0 := by
    unfold diagonalMass
    apply Finset.sum_eq_zero
    intro i _
    rw [strict i i le_rfl, mul_zero]
  apply (ho.visibleClock_reflected_zero_iff ht F cover paid live).mpr
  simp only [groupedColumn_eq_strict_diagonal lower, diagZero, strictZero, leakZero,
    zero_mul, mul_zero, add_zero]

/-- Lower-triangular DIRK client: a *true reflected stop root* kills the
actual diagonal term. Strict cancellation and hidden leakage remain
separate tableau premises. This is not an atom-erasure lemma. -/
theorem dirk_visibleClock_reflected_local_zero (ho : HasOrder p A b)
    (lower : A.IsLowerTriangular)
    {T : Finset K} {t : K} (ht : t ∈ T) (F : K[X])
    (cover : ∀ x, x ∉ T → outputMass A b x = 0)
    (paid : F.natDegree + T.card + 1 ≤ p) (live : outputMass A b t ≠ 0)
    (stopRoot : F.eval (1 - t) = 0)
    (strictZero : strictColumn A b t (F.comp (1 - X)) = 0)
    (leakZero : hiddenLeakage A b T (visibleSelector T t) (F.comp (1 - X)) = 0) :
    integral 0 (1 - t) F = 0 := by
  have atPhysical : (F.comp (1 - X)).eval t = 0 := by
    simpa only [eval_comp, eval_sub, eval_one, eval_X] using stopRoot
  apply (ho.visibleClock_reflected_zero_iff ht F cover paid live).mpr
  simp only [groupedColumn_eq_strict_diagonal lower, atPhysical, strictZero, leakZero,
    zero_mul, mul_zero, add_zero]

end HasOrder
end
end RKResearch
