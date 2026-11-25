module

public import RKCert.ReviewedNative.NativeIntegerAugmentedChecker

@[expose] public section

/-! At the final requested degree, check original scalar payment on
every split basis pair instead of building a terminal row basis.
This terminal cut has no claim about the next degree. -/
namespace RKResearch.Certified.NativeIntegerAugmentedTopPay

open RKResearch
open NativeIntegerSpanClearing NativeIntegerAugmentedChecker RootedTreeAugmentedSpan
open scoped Matrix

def checkTopPair {s : ℕ} (out : ZVec s → ℤ) (d e : ℤ) (p : ℕ)
    (C : Candidate s) (k l : ℕ) : Bool :=
  checkIndices fun i : Fin (C.rank k) =>
    checkIndices fun j : Fin (C.rank l) => checkPayment out e p (joinedZ d C k l i j)

def checkTopPayments {s : ℕ} (out : ZVec s → ℤ) (d e : ℤ) (p : ℕ)
    (C : Candidate s) : Bool :=
  checkDegrees (p-1) fun k => checkTopPair out d e p C k (p-k)

theorem checkTopPayments_get {s p : ℕ} {out : ZVec s → ℤ} {d e : ℤ} {C : Candidate s}
    (h : checkTopPayments out d e p C = true)
    {k l : ℕ} (hk : 0 < k) (hl : 0 < l) (sum : k+l = p)
    (i : Fin (C.rank k)) (j : Fin (C.rank l)) :
    checkPayment out e p (joinedZ d C k l i j) = true := by
  change checkDegrees (p-1) (fun k => checkTopPair out d e p C k (p-k)) = true at h
  have hbound : k ≤ p-1 := by omega
  have eq : p-k = l := by omega
  have take := checkDegrees_get h hk hbound
  rw [eq] at take
  change checkIndices (fun i : Fin (C.rank k) =>
    checkIndices (fun j : Fin (C.rank l) =>
      checkPayment out e p (joinedZ d C k l i j))) = true at take
  exact checkIndices_get (checkIndices_get take i) j

def checkDirectTop {s : ℕ} (act : ZVec s → ZVec s) (out : ZVec s → ℤ)
    (d e : ℤ) (p : ℕ) (C : Candidate s) : Bool :=
  decide (1 < p) &&
    (checkScales d e &&
     (checkLeaf C &&
      (checkActions act p C &&
       (checkProducts d (p-1) C &&
        (checkPayments out e (p-1) C && checkTopPayments out d e p C)))))

theorem checkDirectTop_iff {s : ℕ} (act : ZVec s → ZVec s) (out : ZVec s → ℤ)
    (d e : ℤ) (p : ℕ) (C : Candidate s) :
    checkDirectTop act out d e p C = true ↔
      decide (1 < p) = true ∧ checkScales d e = true ∧ checkLeaf C = true ∧
      checkActions act p C = true ∧ checkProducts d (p-1) C = true ∧
      checkPayments out e (p-1) C = true ∧ checkTopPayments out d e p C = true := by
  simp only [checkDirectTop, Bool.and_eq_true_iff]

/-- Terminal degree is used only as a destination. This proof-only family
may take the whole final paid kernel, with no finite basis for it. -/
def topKernelFamily {s : ℕ} (b : Fin s → ℚ) (e : ℚ) (p : ℕ)
    (B : ℕ → Set (QFeature s)) (n : ℕ) : Set (QFeature s) :=
  if n = p then ((residual b e p).ker : Set (QFeature s)) else B n

theorem topKernelFamily_below {s p n : ℕ} (b : Fin s → ℚ) (e : ℚ)
    (B : ℕ → Set (QFeature s)) (h : n < p) :
    topKernelFamily b e p B n = B n := by
  simp only [topKernelFamily, if_neg (ne_of_lt h)]

theorem topKernelFamily_last {s p : ℕ} (b : Fin s → ℚ) (e : ℚ)
    (B : ℕ → Set (QFeature s)) :
    topKernelFamily b e p B p = ((residual b e p).ker : Set (QFeature s)) := by
  simp [topKernelFamily]

/-- Generic mathematical terminal shortcut: lower closures are unchanged;
only the final ordered pair residuals, rather than final span membership,
are needed. No assumption on the rank of the final actual span. -/
theorem basisCloses_with_direct_top {s : ℕ} (A : Matrix (Fin s) (Fin s) ℚ)
    (b : Fin s → ℚ) (d e : ℚ) (p : ℕ) (B : ℕ → Set (QFeature s))
    (lower : BasisCloses A d (p-1) B)
    (top : ∀ k l : ℕ, 0 < k → 0 < l → k+l = p →
      ∀ x ∈ B k, ∀ y ∈ B l, residual b e p (attachBilin A d l x y) = 0) :
    BasisCloses A d p (topKernelFamily b e p B) := by
  intro k l hk hl hs x hx y hy
  have kb : k < p := by omega
  have lb : l < p := by omega
  rw [topKernelFamily_below b e B kb] at hx
  rw [topKernelFamily_below b e B lb] at hy
  by_cases hsum : k+l = p
  · rw [hsum, topKernelFamily_last]
    exact Submodule.subset_span (LinearMap.mem_ker.mpr (top k l hk hl hsum x hx y hy))
  · have small : k+l < p := by omega
    have small' : k+l ≤ p-1 := by omega
    rw [topKernelFamily_below b e B small]
    exact lower k l hk hl small' x hx y hy

theorem checkTopPayments_sound {s p : ℕ} (A : Matrix (Fin s) (Fin s) ℤ)
    (b : ZVec s) (act : ZVec s → ZVec s) (out : ZVec s → ℤ)
    (hact : ∀ v, act v = A *ᵥ v) (hout : ∀ v, out v = b ⬝ᵥ v)
    (d e : ℤ) (C : Candidate s) (ha : checkActions act p C = true)
    (h : checkTopPayments out d e p C = true) :
    ∀ k l : ℕ, 0 < k → 0 < l → k+l = p →
      ∀ x ∈ generators C k, ∀ y ∈ generators C l,
        residual (ratVec b) (e : ℚ) p (attachBilin (ratMatrix A) (d : ℚ) l x y) = 0 := by
  intro k l hk hl sum x hx y hy
  change x ∈ Set.range (fun i => ratFeature (C.rows k i)) at hx
  change y ∈ Set.range (fun j => ratFeature (C.rows l j)) at hy
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  have hlp : l < p := by omega
  have rhs := checkPayment_sound b out hout e p (joinedZ d C k l i j)
    (checkTopPayments_get h hk hl sum i j)
  rw [joinedZ_sound A act hact d C k l i j (checkActions_get ha hl hlp j)] at rhs
  exact rhs

theorem hasOrder_of_direct_top_check {s : ℕ} (A : Matrix (Fin s) (Fin s) ℤ)
    (b : ZVec s) (act : ZVec s → ZVec s) (out : ZVec s → ℤ)
    (hact : ∀ v, act v = A *ᵥ v) (hout : ∀ v, out v = b ⬝ᵥ v)
    (d e : ℤ) (p : ℕ) (C : Candidate s)
    {U : Matrix (Fin s) (Fin s) ℚ} {w : Fin s → ℚ}
    (hA : ratMatrix A = (d : ℚ) • U) (hb : ratVec b = (e : ℚ) • w)
    (h : checkDirectTop act out d e p C = true) : RKResearch.HasOrder p U w := by
  obtain ⟨p_dec, sc, first, acts, prod, paid, last⟩ := (checkDirectTop_iff act out d e p C).mp h
  have ppos : 1 < p := of_decide_eq_true p_dec
  obtain ⟨hd, he⟩ := checkScales_sound sc
  let D := topKernelFamily (ratVec b) (e : ℚ) p (generators C)
  have base : ((1 : Fin s → ℚ), (1 : ℚ)) ∈ Submodule.span ℚ (D 1) := by
    change _ ∈ Submodule.span ℚ (topKernelFamily (ratVec b) (e : ℚ) p (generators C) 1)
    rw [topKernelFamily_below (ratVec b) (e : ℚ) (generators C) ppos]
    exact checkLeaf_sound first
  have lower_bound : p-1 ≤ p := Nat.sub_le _ _
  have lower := checkProducts_sound A act hact d C lower_bound acts prod
  have top := checkTopPayments_sound A b act out hact hout d e C acts last
  have close : BasisCloses (ratMatrix A) (d : ℚ) p D :=
    basisCloses_with_direct_top (ratMatrix A) (ratVec b) (d : ℚ) (e : ℚ) p (generators C) lower top
  have qpaid : ∀ n : ℕ, 0 < n → n ≤ p → ∀ x ∈ D n,
      residual (ratVec b) (e : ℚ) n x = 0 := by
    intro n hn hp x hx
    change x ∈ topKernelFamily (ratVec b) (e : ℚ) p (generators C) n at hx
    by_cases eq : n = p
    · subst n
      rw [topKernelFamily_last] at hx
      exact LinearMap.mem_ker.mp hx
    · have below : n < p := by omega
      have below' : n ≤ p-1 := by omega
      rw [topKernelFamily_below (ratVec b) (e : ℚ) (generators C) below] at hx
      exact checkPayments_sound b out hout e C paid n hn below' x hx
  have moments := all_scaled_moments_of_basis_closure (ratMatrix A) (ratVec b)
    (d : ℚ) (e : ℚ) p D base close qpaid
  exact original_order_from_rational_scaled_moments A b d e p hA hb hd he moments

end RKResearch.Certified.NativeIntegerAugmentedTopPay
