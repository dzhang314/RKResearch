module

public import RKCert.ReviewedNative.DefectBudget

@[expose] public section

/-! # Extending the graded part of a reviewed defect certificate -/
namespace RKResearch.Certified.Graded

variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- A graded prefix independent of the weight row. The first two spaces
are zero, as true reviewed defects first occur in grade two. -/
structure DefectPrefix (B : Matrix ι ι R) (n : ℕ) where
  space : ℕ → Submodule R (ι → R)
  zero : space 0 = ⊥
  one : space 1 = ⊥
  clock : ∀ j, j + 1 < n → space j ≤ (space (j + 1)).comap (diag (nodes B))
  advance : ∀ j, j + 1 < n → space j ≤ (space (j + 1)).comap (mat B)
  primitive : ∀ j, j + 1 < n → monomialStageDefect B j ∈ space (j + 1)
  product : ∀ j k, j + k < n → ProductsIn (space j) (space k) (space (j + k))

namespace DefectPrefix

variable {B : Matrix ι ι R} {n : ℕ}

theorem low_zero (P : DefectPrefix B n) {j : ℕ} (hj : j < 2) :
    P.space j = ⊥ := by
  have e : j = 0 ∨ j = 1 := by omega
  rcases e with rfl | rfl
  · exact P.zero
  · exact P.one

def appendedSpace (P : DefectPrefix B n) (W : Submodule R (ι → R)) (j : ℕ) :
    Submodule R (ι → R) :=
  if j < n then P.space j else W

/-- Append one grade. Only the old top grade, the new primitive, and
products with this exact new total grade require receipts. -/
def append (P : DefectPrefix B n) (hn : 2 ≤ n) (W : Submodule R (ι → R))
    (hC : P.space (n - 1) ≤ W.comap (diag (nodes B)))
    (hB : P.space (n - 1) ≤ W.comap (mat B))
    (hE : monomialStageDefect B (n - 1) ∈ W)
    (hP : ∀ j k, 2 ≤ j → 2 ≤ k → j + k = n →
      ProductsIn (P.space j) (P.space k) W) : DefectPrefix B (n + 1) where
  space := P.appendedSpace W
  zero := by simp only [appendedSpace, if_pos (show 0 < n by omega), P.zero]
  one := by simp only [appendedSpace, if_pos (show 1 < n by omega), P.one]
  clock := by
    intro j hj
    have h₀ : j < n := by omega
    by_cases h₁ : j + 1 < n
    · simpa only [appendedSpace, if_pos h₀, if_pos h₁] using P.clock j h₁
    · have h₂ : j + 1 = n := by omega
      have h₃ : j = n - 1 := by omega
      rw [appendedSpace, if_pos h₀, appendedSpace, if_neg h₁, h₃]
      exact hC
  advance := by
    intro j hj
    have h₀ : j < n := by omega
    by_cases h₁ : j + 1 < n
    · simpa only [appendedSpace, if_pos h₀, if_pos h₁] using P.advance j h₁
    · have h₂ : j + 1 = n := by omega
      have h₃ : j = n - 1 := by omega
      rw [appendedSpace, if_pos h₀, appendedSpace, if_neg h₁, h₃]
      exact hB
  primitive := by
    intro j hj
    by_cases h₁ : j + 1 < n
    · simpa only [appendedSpace, if_pos h₁] using P.primitive j h₁
    · have h₃ : j = n - 1 := by omega
      rw [appendedSpace, if_neg h₁, h₃]
      exact hE
  product := by
    intro j k hjk v w hv hw
    by_cases h₀ : j + k < n
    · have hj : j < n := by omega
      have hk : k < n := by omega
      simp only [appendedSpace, if_pos hj] at hv
      simp only [appendedSpace, if_pos hk] at hw
      simpa only [appendedSpace, if_pos h₀] using P.product j k h₀ hv hw
    · have he : j + k = n := by omega
      change v * w ∈ P.appendedSpace W (j + k)
      rw [appendedSpace, if_neg h₀]
      by_cases hj : j < 2
      · have hj' : j < n := by omega
        have hz : v = 0 := by
          apply (Submodule.mem_bot R).mp
          simpa only [appendedSpace, if_pos hj', P.low_zero hj] using hv
        rw [hz, zero_mul]
        exact W.zero_mem
      by_cases hk : k < 2
      · have hk' : k < n := by omega
        have hz : w = 0 := by
          apply (Submodule.mem_bot R).mp
          simpa only [appendedSpace, if_pos hk', P.low_zero hk] using hw
        rw [hz, mul_zero]
        exact W.zero_mem
      have hj' : j < n := by omega
      have hk' : k < n := by omega
      simp only [appendedSpace, if_pos hj'] at hv
      simp only [appendedSpace, if_pos hk'] at hw
      exact hP j k (by omega) (by omega) he hv hw

theorem append_space (P : DefectPrefix B n) (hn : 2 ≤ n) (W : Submodule R (ι → R))
    (hC : P.space (n - 1) ≤ W.comap (diag (nodes B)))
    (hB : P.space (n - 1) ≤ W.comap (mat B))
    (hE : monomialStageDefect B (n - 1) ∈ W)
    (hP : ∀ j k, 2 ≤ j → 2 ≤ k → j + k = n →
      ProductsIn (P.space j) (P.space k) W) (j : ℕ) :
    (P.append hn W hC hB hE hP).space j = if j < n then P.space j else W := rfl

/-- Attach the output-row annihilation to a genuine graded prefix. -/
def toFiltration (P : DefectPrefix B n) (b : ι → R)
    (hs : ∀ j, j < n → P.space j ≤ probeCut B b 0) : DefectFiltration B b n where
  space := P.space
  clock := P.clock
  advance := P.advance
  primitive := P.primitive
  product := P.product
  silent := by
    intro j hj
    rw [← probeCut_zero B b]
    exact hs j hj

end DefectPrefix

/-- The common two-grade tail. Products involving either of the two new
spaces need no separate check: any nonzero defect partner costs at least
two grades, and would exceed the budget. -/
structure DefectTailTwo {B : Matrix ι ι R} {n : ℕ} (P : DefectPrefix B n)
    (b : ι → R) (z : R) : Prop where
  quadrature : ScaledClockMoments B b z (n + 2)
  adjoint : ScaledD1 B b z
  prefix_silent : ∀ j, j < n → P.space j ≤ probeCut B b 0
  last_two : P.space (n - 1) ≤ probeCut B b 2
  advance_last : P.space (n - 1) ≤ (probeCut B b 1).comap (mat B)
  primitive_last : monomialStageDefect B (n - 1) ∈ probeCut B b 1
  product_one : ∀ j k, 2 ≤ j → 2 ≤ k → j + k = n →
    ProductsIn (P.space j) (P.space k) (probeCut B b 1)
  product_zero : ∀ j k, 2 ≤ j → 2 ≤ k → j + k = n + 1 →
    ProductsIn (P.space j) (P.space k) (probeCut B b 0)

namespace DefectTailTwo

variable {B : Matrix ι ι R} {n : ℕ} {P : DefectPrefix B n} {b : ι → R} {z : R}

def first (h : DefectTailTwo P b z) (hn : 2 ≤ n) : DefectPrefix B (n + 1) :=
  P.append hn (probeCut B b 1) (h.last_two.trans (probeCut_clock B b 1))
    h.advance_last h.primitive_last h.product_one

/-- Complete the genuine prefix by K₁,K₀. D1 handles the final primitive
and all final primitive advances. -/
def complete (h : DefectTailTwo P b z) (hn : 2 ≤ n) : DefectFiltration B b (n + 2) := by
  let U := h.first hn
  have eU (j : ℕ) : U.space j = if j < n then P.space j else probeCut B b 1 := rfl
  have last : U.space (n + 1 - 1) = probeCut B b 1 := by
    rw [show n + 1 - 1 = n from by omega, eU, if_neg (Nat.lt_irrefl n)]
  have pprod : ∀ j k, 2 ≤ j → 2 ≤ k → j + k = n + 1 →
      ProductsIn (U.space j) (U.space k) (probeCut B b 0) := by
    intro j k hj hk he
    rw [eU j, eU k, if_pos (show j < n by omega), if_pos (show k < n by omega)]
    exact h.product_zero j k hj hk he
  let T := U.append (by omega) (probeCut B b 0)
    (by rw [last]; exact probeCut_clock B b 0)
    (by rw [last]; exact h.adjoint.advance_cut)
    (by
      rw [show n + 1 - 1 = n from by omega, probeCut_zero, LinearMap.mem_ker]
      exact h.adjoint.primitive_mass h.quadrature n (by omega)) pprod
  have eT (j : ℕ) : T.space j = if j < n + 1 then U.space j else probeCut B b 0 := rfl
  refine T.toFiltration b (fun j hj => ?_)
  rw [eT]
  by_cases hj₁ : j < n + 1
  · rw [if_pos hj₁, eU]
    by_cases hj₀ : j < n
    · rw [if_pos hj₀]
      exact h.prefix_silent j hj₀
    · rw [if_neg hj₀]
      exact probeCut_anti B b (by decide : 0 ≤ 1)
  · simp only [if_neg hj₁, le_rfl]

theorem hasOrder_of_scale {A : Matrix ι ι R}
    {P : DefectPrefix (z • A) n} (h : DefectTailTwo P b z)
    (hn : 2 ≤ n) (hz : IsLeftRegular z) : RKResearch.HasOrder (n + 2) A b :=
  (h.complete hn).hasOrder_of_smul hz h.quadrature

end DefectTailTwo
end RKResearch.Certified.Graded
