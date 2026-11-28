module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8PhysicalCount

open scoped Matrix BigOperators

/-- The first quadratic defect of a lower-triangular tableau uses only
its literal first diagonal. This statement is cleared of division. -/
theorem firstQuadraticDefectCleared {R : Type*} [CommRing R] {s : ℕ}
    (A : Matrix (Fin (s + 1)) (Fin (s + 1)) R) (γ : R)
    (hA : ∀ i j, i < j → A i j = 0) (hγ : A 0 0 = γ) :
    let c := A *ᵥ (fun _ => (1 : R))
    2 * (A *ᵥ c) 0 - c 0 ^ 2 = γ ^ 2 := by
  let c := A *ᵥ (fun _ => (1 : R))
  have row_zero (v : Fin (s + 1) → R) : (A *ᵥ v) 0 = γ * v 0 := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single 0]
    · rw [hγ]
    · intro j _ hj
      rw [hA 0 j (lt_of_le_of_ne (Fin.zero_le _) (Ne.symm hj)), zero_mul]
    · simp
  have hc : c 0 = γ := by rw [show c 0 = _ from row_zero _]; simp
  change 2 * (A *ᵥ c) 0 - c 0 ^ 2 = γ ^ 2
  rw [row_zero, hc]
  ring

/-- Once counts one through seven have been excluded, the literal first
row eliminates count ten. This does not exclude the counts 0, 8, or 9. -/
theorem survivingCounts {K : Type*} [Field K] [DecidableEq K] (A : Matrix (Fin 10) (Fin 10) K)
    (γ : K) (hγ : A 0 0 = γ) (hnz : γ ≠ 0) (h2 : (2 : K) ≠ 0)
    (hA : ∀ i j, i < j → A i j = 0)
    (hexcl : let c := A *ᵥ (fun _ => (1 : K))
             let g := fun i => (A *ᵥ c) i - c i ^ 2 / 2
             let n := (Finset.univ.filter fun i => g i = 0).card
             n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 4 ∧ n ≠ 5 ∧ n ≠ 6 ∧ n ≠ 7) :
    let c := A *ᵥ (fun _ => (1 : K))
    let g := fun i => (A *ᵥ c) i - c i ^ 2 / 2
    let n := (Finset.univ.filter fun i => g i = 0).card
    n = 0 ∨ n = 8 ∨ n = 9 := by
  let c := A *ᵥ (fun _ => (1 : K))
  let g := fun i => (A *ᵥ c) i - c i ^ 2 / 2
  let S := (Finset.univ : Finset (Fin 10)).filter fun i => g i = 0
  change S.card = 0 ∨ S.card = 8 ∨ S.card = 9
  change S.card ≠ 1 ∧ S.card ≠ 2 ∧ S.card ≠ 3 ∧ S.card ≠ 4 ∧
    S.card ≠ 5 ∧ S.card ≠ 6 ∧ S.card ≠ 7 at hexcl
  have H : 2 * g 0 = γ ^ 2 := by
    have hf := firstQuadraticDefectCleared (s := 9) A γ hA hγ
    change 2 * (A *ᵥ c) 0 - c 0 ^ 2 = γ ^ 2 at hf
    unfold g
    calc
      2 * ((A *ᵥ c) 0 - c 0 ^ 2 / 2) = 2 * (A *ᵥ c) 0 - c 0 ^ 2 := by
        field_simp
      _ = γ ^ 2 := hf
  have hg : g 0 ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at H
    exact (pow_ne_zero 2 hnz) H.symm
  have hbound : S.card < 10 := by
    have hsub : S ⊂ (Finset.univ : Finset (Fin 10)) := by
      apply Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
      intro h
      have hnot : 0 ∉ S := by simpa [S] using hg
      exact hnot (h.symm ▸ Finset.mem_univ _)
    simpa using Finset.card_lt_card hsub
  omega

end RKCert.ReviewedNative.SDIRK8PhysicalCount

#print axioms RKCert.ReviewedNative.SDIRK8PhysicalCount.firstQuadraticDefectCleared
#print axioms RKCert.ReviewedNative.SDIRK8PhysicalCount.survivingCounts
