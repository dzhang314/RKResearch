module

public import RKCert.ReviewedNative.PositiveIntervalGrid19
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.SignVariations

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.NormNum

@[expose] public section

/-! # Shared sign windows on an exact positive grid

The sample vocabulary uses the existing interval grid and defines no new rule.
-/
namespace RKCert.ReviewedNative.FiniteOrderedSigns

open Polynomial RKCert.Endpoint
open RKCert.ReviewedNative.PositiveRule19
open scoped BigOperators

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- An increasing sample list need not avoid roots; the Mathlib count
ignores zero sample values. -/
def variation (P : K[X]) (xs : List K) : ℕ :=
  (xs.map P.eval).signVariations

/-- A witnessed lower bound on variations in an arbitrary set. Both open
windows and their closed endpoint extensions use this single predicate. -/
def HasAlternationsOn (P : K[X]) (S : Set K) (m : ℕ) : Prop :=
  ∃ xs : List K, xs.Pairwise (· < ·) ∧ (∀ x ∈ xs, x ∈ S) ∧ m ≤ variation P xs

omit [IsStrictOrderedRing K] in
theorem HasAlternationsOn.mono {P : K[X]} {S T : Set K} {m n : ℕ}
    (h : HasAlternationsOn P S m) (sub : S ⊆ T) (le : n ≤ m) :
    HasAlternationsOn P T n := by
  obtain ⟨xs, increasing, inside, alt⟩ := h
  exact ⟨xs, increasing, fun x hx => sub (inside x hx), le.trans alt⟩

/-- Exactly the nodes of `PositiveIntervalGrid19`, in their increasing order. -/
def gridSamples (l r : K) : List K := List.ofFn (intervalPoint l r)

def gridVariation (P : K[X]) (l r : K) : ℕ := variation P (gridSamples l r)

omit [IsStrictOrderedRing K] in
theorem gridVariation_eq (P : K[X]) (l r : K) :
    gridVariation P l r =
      (List.ofFn (fun i : Fin 19 => P.eval (intervalPoint l r i))).signVariations := by
  simp only [gridVariation, variation, gridSamples, List.map_ofFn, Function.comp_def]

theorem gridSamples_increasing {l r : K} (lr : l < r) :
    (gridSamples l r).Pairwise (· < ·) :=
  List.pairwise_ofFn.mpr (intervalPoint_strictMono lr)

theorem gridSamples_inside {l r : K} (lr : l < r) (x : K) (hx : x ∈ gridSamples l r) :
    x ∈ Set.Ioo l r := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact intervalPoint_mem lr i

theorem HasAlternationsOn.of_grid {l r : K} (lr : l < r) {P : K[X]} {m : ℕ}
    (h : m ≤ gridVariation P l r) : HasAlternationsOn P (Set.Ioo l r) m :=
  ⟨gridSamples l r, gridSamples_increasing lr, fun x hx => gridSamples_inside lr x hx, h⟩

/-- One genuine sample survives: nineteen distinct nodes determine a
polynomial of degree less than nineteen without needing real roots. -/
theorem exists_nonzero_grid_sample {l r : K} (lr : l < r) {P : K[X]}
    (pn : P ≠ 0) (small : P.natDegree < 19) :
    ∃ i : Fin 19, P.eval (intervalPoint l r i) ≠ 0 := by
  classical
  by_cases yes : ∃ i : Fin 19, P.eval (intervalPoint l r i) ≠ 0
  · exact yes
  exfalso
  apply pn
  let S : Finset (Fin 19) := Finset.univ
  have sd : P.natDegree < S.card := by simpa [S] using small
  have pd : P.degree < (S.card : WithBot ℕ) :=
    P.degree_le_natDegree.trans_lt (by exact_mod_cast sd)
  refine Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero S
    (intervalPoint_strictMono lr).injective.injOn pd ?_
  intro i _
  by_contra ih
  exact yes ⟨i, ih⟩

/-- The exact ordered moment detects a strictly positive term on a
nonnegative sample grid. This step does not claim pointwise positivity
between the samples. -/
theorem integral_pos_of_grid_samples {l r : K} (lr : l < r) {G : K[X]}
    (degree : G.natDegree ≤ 19)
    (h : ∀ i : Fin 19, 0 ≤ G.eval (intervalPoint l r i))
    (live : ∃ i : Fin 19, 0 < G.eval (intervalPoint l r i)) :
    0 < integral l r G := by
  rw [interval_exact l r G degree]
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (intervalWeight_pos lr i).le (h i)
  · obtain ⟨i, hi⟩ := live
    exact ⟨i, Finset.mem_univ _, mul_pos (intervalWeight_pos lr i) hi⟩

/-- Separators retain their actual physical sample positions. A cut is the
midpoint of a pair of consecutive *nonzero* samples of opposite signs. -/
structure SignCuts {n : ℕ} (x y : Fin n → K) where
  points : Finset K
  orientation : K
  orientationSign : orientation = 1 ∨ orientation = -1
  count : points.card = (List.ofFn y).signVariations
  mem_iff : ∀ t, t ∈ points ↔ ∃ i j : Fin n,
    i < j ∧ y i*y j < 0 ∧ (∀ k, i < k → k < j → y k=0) ∧ t=(x i+x j)/2
  separates : ∀ i, y i ≠ 0 → 0 < y i*((C orientation*nodalHull points).eval (x i))

namespace SignCuts
variable {n : ℕ} {x y : Fin n → K}

def polynomial (cuts : SignCuts x y) : K[X] := C cuts.orientation*nodalHull cuts.points

omit [IsStrictOrderedRing K] in
theorem natDegree_polynomial_le (cuts : SignCuts x y) :
    cuts.polynomial.natDegree ≤ (List.ofFn y).signVariations := by
  unfold polynomial
  exact natDegree_mul_le.trans (by rw [natDegree_C, natDegree_nodalHull, zero_add, cuts.count])

end SignCuts


end
end RKCert.ReviewedNative.FiniteOrderedSigns
