import RKCert.Research.WeightedOrderNineGram
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace RKResearch.WeightedOrderNineGram

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def sumFive (f : Fin 5 → K) : K := f 0 + f 1 + f 2 + f 3 + f 4

def coordinate (a : Fin 5 → K) (k : Fin 5) : K :=
  sumFive fun i => ((lower i k : Rat) : K) * a i

theorem cast_factorization (i j : Fin 5) :
    ((gram i j : Rat) : K) =
      sumFive (fun k => (lower i k : K) * (diagonal k : K) * (lower j k : K)) := by
  have h := congrArg (fun q : Rat => (q : K)) (factorization i j)
  simpa only [sum5, sumFive, Rat.cast_add, Rat.cast_mul] using h

theorem quadratic_eq (a : Fin 5 → K) :
    sumFive (fun i => sumFive (fun j => a i * (gram i j : K) * a j)) =
      sumFive (fun k => (diagonal k : K) * coordinate a k ^ 2) := by
  simp only [cast_factorization, coordinate, sumFive]
  ring

omit [IsStrictOrderedRing K] in
theorem coordinate_exists_ne_zero (a : Fin 5 → K) (ha : ∃ i, a i ≠ 0) :
    ∃ k, coordinate a k ≠ 0 := by
  by_contra! hh
  have h4 := hh (4 : Fin 5)
  have e4 : a 4 = 0 := by
    simp only [coordinate, sumFive] at h4
    rw [lower_strict_upper_zero (0 : Fin 5) 4 (by decide)] at h4
    rw [lower_strict_upper_zero (1 : Fin 5) 4 (by decide)] at h4
    rw [lower_strict_upper_zero (2 : Fin 5) 4 (by decide)] at h4
    rw [lower_strict_upper_zero (3 : Fin 5) 4 (by decide)] at h4
    rw [lower_unit_diagonal (4 : Fin 5)] at h4
    simpa [] using h4
  have h3 := hh (3 : Fin 5)
  have e3 : a 3 = 0 := by
    simp only [coordinate, sumFive] at h3
    rw [lower_strict_upper_zero (0 : Fin 5) 3 (by decide)] at h3
    rw [lower_strict_upper_zero (1 : Fin 5) 3 (by decide)] at h3
    rw [lower_strict_upper_zero (2 : Fin 5) 3 (by decide)] at h3
    rw [lower_unit_diagonal (3 : Fin 5)] at h3
    simpa [e4] using h3
  have h2 := hh (2 : Fin 5)
  have e2 : a 2 = 0 := by
    simp only [coordinate, sumFive] at h2
    rw [lower_strict_upper_zero (0 : Fin 5) 2 (by decide)] at h2
    rw [lower_strict_upper_zero (1 : Fin 5) 2 (by decide)] at h2
    rw [lower_unit_diagonal (2 : Fin 5)] at h2
    simpa [e3, e4] using h2
  have h1 := hh (1 : Fin 5)
  have e1 : a 1 = 0 := by
    simp only [coordinate, sumFive] at h1
    rw [lower_strict_upper_zero (0 : Fin 5) 1 (by decide)] at h1
    rw [lower_unit_diagonal (1 : Fin 5)] at h1
    simpa [e2, e3, e4] using h1
  have h0 := hh (0 : Fin 5)
  have e0 : a 0 = 0 := by
    simp only [coordinate, sumFive] at h0
    rw [lower_unit_diagonal (0 : Fin 5)] at h0
    simpa [e1, e2, e3, e4] using h0
  obtain ⟨i, hi⟩ := ha
  fin_cases i <;> contradiction

theorem quadratic_pos (a : Fin 5 → K) (ha : ∃ i, a i ≠ 0) :
    0 < sumFive (fun i => sumFive (fun j => a i * (gram i j : K) * a j)) := by
  rw [quadratic_eq]
  let term (i : Fin 5) := (diagonal i : K) * coordinate a i ^ 2
  have hw (i) : 0 < (diagonal i : K) := by exact_mod_cast diagonal_positive i
  have hz (i) : 0 ≤ term i := mul_nonneg (le_of_lt (hw i)) (sq_nonneg _)
  obtain ⟨k, hk⟩ := coordinate_exists_ne_zero a ha
  have hp : 0 < term k := mul_pos (hw k) (sq_pos_of_ne_zero hk)
  change 0 < term 0 + term 1 + term 2 + term 3 + term 4
  fin_cases k
  · have hpos : 0 < term 0 := hp
    linarith only [hpos, hz 0, hz 1, hz 2, hz 3, hz 4]
  · have hpos : 0 < term 1 := hp
    linarith only [hpos, hz 0, hz 1, hz 2, hz 3, hz 4]
  · have hpos : 0 < term 2 := hp
    linarith only [hpos, hz 0, hz 1, hz 2, hz 3, hz 4]
  · have hpos : 0 < term 3 := hp
    linarith only [hpos, hz 0, hz 1, hz 2, hz 3, hz 4]
  · have hpos : 0 < term 4 := hp
    linarith only [hpos, hz 0, hz 1, hz 2, hz 3, hz 4]

end RKResearch.WeightedOrderNineGram

#print axioms RKResearch.WeightedOrderNineGram.quadratic_pos
