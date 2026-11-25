module

public import RKCert.ReviewedNative.PaidDefectBridge
public import Mathlib.LinearAlgebra.Span.Basic

@[expose] public section

namespace RKResearch.Certified.AllowedTapSpan

open RKResearch FiniteRootedTree
open RKResearch.Certified.PaidDefectBridge
open RKResearch.Certified.Graded (row)
open scoped Matrix BigOperators

section Assembly

variable {K : Type*} [Semiring K] {Tap : Type*} [Fintype Tap]
  {M : Type*} [AddCommMonoid M] [Module K M]

/-- The coefficient-support map for a finite allowed family. -/
def assembly (B : Tap → M) : (Tap → K) →ₗ[K] M where
  toFun := fun c => ∑ a : Tap, c a • B a
  map_add' := by
    intro c d
    change (∑ a : Tap, (c a + d a) • B a) =
      (∑ a : Tap, c a • B a) + ∑ a : Tap, d a • B a
    simp only [add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro k c
    change (∑ a : Tap, (k * c a) • B a) = k • (∑ a : Tap, c a • B a)
    simp only [mul_smul, Finset.smul_sum]

theorem assembly_apply (B : Tap → M) (c : Tap → K) :
    assembly B c = ∑ a : Tap, c a • B a := rfl

/-- No independence or numerical rank test is needed to recover the
coefficient vector from span membership. -/
theorem range_assembly_eq_span (B : Tap → M) :
    LinearMap.range (assembly (K := K) B) = Submodule.span K (Set.range B) := by
  classical
  apply le_antisymm
  · intro m hm
    rcases LinearMap.mem_range.mp hm with ⟨c,rfl⟩
    rw [assembly_apply]
    apply (Submodule.span K (Set.range B)).sum_mem
    intro a _
    exact (Submodule.span K (Set.range B)).smul_mem (c a)
      (Submodule.subset_span ⟨a,rfl⟩)
  · apply Submodule.span_le.2
    rintro _ ⟨a,rfl⟩
    apply LinearMap.mem_range.mpr
    refine ⟨fun i => if i = a then (1 : K) else 0, ?_⟩
    rw [assembly_apply, Finset.sum_eq_single a]
    · simp
    · intro i _ hi
      simp [hi]
    · simp

theorem mem_span_iff_exists_assembly (B : Tap → M) (target : M) :
    target ∈ Submodule.span K (Set.range B) ↔
      ∃ c : Tap → K, assembly B c = target := by
  have h : target ∈ LinearMap.range (assembly (K := K) B) ↔
      ∃ c : Tap → K, assembly B c = target := LinearMap.mem_range
  simpa only [range_assembly_eq_span B] using h

end Assembly

section Matrices

variable {K : Type*} [Semiring K] {U V : Type*} [Fintype U] [Fintype V]
  {Tap : Type*} [Fintype Tap]

/-- One actual allowed evaluation tensor, including its output site weight. -/
def tapColumn (weight : K) (forwardEval : U → K) (reverseEval : V → K) :
    Matrix U V K :=
  fun i j => weight * forwardEval i * reverseEval j

def matrixPair (M : Matrix U V K) (a : U → K) (b : V → K) : K :=
  ∑ i : U, ∑ j : V, a i * M i j * b j

theorem matrixPair_zero (a : U → K) (b : V → K) :
    matrixPair (0 : Matrix U V K) a b = 0 := by
  simp [matrixPair]

/-- The rank-free, square-coordinate certificate interface. -/
noncomputable def cellMatrix (u : U) (v : V) : Matrix U V K := by
  classical
  exact fun i j => if i = u ∧ j = v then 1 else 0

theorem sum_cellMatrix (target : Matrix U V K) :
    (∑ i : U, ∑ j : V, target i j • cellMatrix (K := K) i j) = target := by
  classical
  ext u v
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single u]
  · rw [Finset.sum_eq_single v]
    · simp [cellMatrix]
    · intro j _ hj
      simp [cellMatrix, Ne.symm hj]
    · simp
  · intro i _ hi
    simp [cellMatrix, Ne.symm hi]
  · simp

theorem mem_span_of_cell_mem (B : Tap → Matrix U V K)
    (target : Matrix U V K)
    (hcell : ∀ i j, cellMatrix (K := K) i j ∈ Submodule.span K (Set.range B)) :
    target ∈ Submodule.span K (Set.range B) := by
  rw [← sum_cellMatrix target]
  apply (Submodule.span K (Set.range B)).sum_mem
  intro i _
  apply (Submodule.span K (Set.range B)).sum_mem
  intro j _
  exact (Submodule.span K (Set.range B)).smul_mem (target i j) (hcell i j)

/-- Combine the certified coefficients of the standard cells, explicitly. -/
def coefficientsOfCells (target : Matrix U V K)
    (cellCoeff : U → V → Tap → K) : Tap → K :=
  ∑ i : U, ∑ j : V, target i j • cellCoeff i j

theorem assembly_coefficientsOfCells (B : Tap → Matrix U V K)
    (target : Matrix U V K) (cellCoeff : U → V → Tap → K)
    (hcell : ∀ i j, assembly B (cellCoeff i j) = cellMatrix (K := K) i j) :
    assembly B (coefficientsOfCells target cellCoeff) = target := by
  simp only [coefficientsOfCells, map_sum, map_smul, hcell, sum_cellMatrix]

/-- To certify a full basis, supply exact allowed coefficients for each cell. -/
theorem mem_span_of_cell_coeffs (B : Tap → Matrix U V K)
    (target : Matrix U V K) (cellCoeff : U → V → Tap → K)
    (hcell : ∀ i j, assembly B (cellCoeff i j) = cellMatrix (K := K) i j) :
    target ∈ Submodule.span K (Set.range B) := by
  exact (mem_span_iff_exists_assembly B target).2
    ⟨coefficientsOfCells target cellCoeff, assembly_coefficientsOfCells B target cellCoeff hcell⟩

end Matrices

section Order

variable {K : Type*} [Field K] {F S U V Tap : Type*}
  [Fintype F] [Fintype S] [Fintype U] [Fintype V] [Fintype Tap]

abbrev paidTapWord (A : Matrix (F ⊕ S) (F ⊕ S) K) (w ξ : S → K)
    (t : FiniteRootedTree) (W : List Letter) : K :=
  row w (wordMap (suffixBlock A) ξ W (primitiveSeed A ξ t))

def LowSeedZero (q : ℕ) (A : Matrix (F ⊕ S) (F ⊕ S) K) (ξ : S → K) : Prop :=
  ∀ t, treeSize t ≤ q → primitiveSeed A ξ t = 0

def ShortTapPayments (q r : ℕ) (A : Matrix (F ⊕ S) (F ⊕ S) K)
    (w ξ : S → K) : Prop :=
  ∀ (t : FiniteRootedTree) (W : List Letter),
    q < treeSize t → W.length + treeSize t < q + r + 2 →
    W.length < r → paidTapWord A w ξ t W = 0

/-- Actual top payment represented in a small, supplied residual basis. -/
def TopTapExpansion (q r : ℕ) (A : Matrix (F ⊕ S) (F ⊕ S) K)
    (w ξ : S → K) (fc : FiniteRootedTree → U → K)
    (rc : List Letter → V → K) (M : Matrix U V K) : Prop :=
  ∀ (t : FiniteRootedTree) (W : List Letter), treeSize t = q + 1 → W.length = r →
    paidTapWord A w ξ t W = matrixPair M (fc t) (rc W)

/-- Direct route for an already selected exact coefficient vector and its
actual matrix. No order predicate is a premise. -/
theorem hasOrder_of_tap_coeffs [CharZero K] {q r : ℕ} (hband : r ≤ q)
    (A : Matrix (F ⊕ S) (F ⊕ S) K) (w ξ : S → K)
    (fc : FiniteRootedTree → U → K) (rc : List Letter → V → K)
    (B : Tap → Matrix U V K) (target : Matrix U V K) (c : Tap → K)
    (hquad : HasQuadratureOrder (q + r + 2) w ξ)
    (hlow : LowSeedZero q A ξ)
    (hshort : ShortTapPayments q r A w ξ)
    (htop : TopTapExpansion q r A w ξ fc rc (assembly B c - target))
    (hc : assembly B c = target) :
    HasOrder (q + r + 2) A (Sum.elim (0 : F → K) w) := by
  apply hasOrder_of_paid_defect_words (p := q + r + 2) (q := q)
    A w ξ (by omega) hquad
  · intro t ht _
    exact hlow t ht
  · intro t W ht hb
    change paidTapWord A w ξ t W = 0
    by_cases hs : W.length < r
    · exact hshort t W ht hb hs
    · have hts : treeSize t = q + 1 := by omega
      have hws : W.length = r := by omega
      rw [htop t W hts hws, hc, sub_self]
      exact matrixPair_zero (fc t) (rc W)

/-- Span sufficiency for a supplied actual assembler. The hypotheses
certify only the emitted table's structural payments, not its full order. -/
theorem exists_hasOrder_of_tap_span [CharZero K] {q r : ℕ} (hband : r ≤ q)
    (A : (Tap → K) → Matrix (F ⊕ S) (F ⊕ S) K) (w ξ : S → K)
    (fc : FiniteRootedTree → U → K) (rc : List Letter → V → K)
    (B : Tap → Matrix U V K) (target : Matrix U V K)
    (hquad : HasQuadratureOrder (q + r + 2) w ξ)
    (hspan : target ∈ Submodule.span K (Set.range B))
    (hstructure : ∀ c, assembly B c = target →
      LowSeedZero q (A c) ξ ∧ ShortTapPayments q r (A c) w ξ ∧
        TopTapExpansion q r (A c) w ξ fc rc (assembly B c - target)) :
    ∃ c, assembly B c = target ∧
      HasOrder (q + r + 2) (A c) (Sum.elim (0 : F → K) w) := by
  obtain ⟨c,hc⟩ := (mem_span_iff_exists_assembly B target).1 hspan
  obtain ⟨hlow,hshort,htop⟩ := hstructure c hc
  exact ⟨c,hc,hasOrder_of_tap_coeffs hband (A c) w ξ fc rc B target c
    hquad hlow hshort htop hc⟩

end Order

end RKResearch.Certified.AllowedTapSpan
