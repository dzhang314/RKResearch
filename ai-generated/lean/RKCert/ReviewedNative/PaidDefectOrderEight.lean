module

public import RKCert.ReviewedNative.PaidDefectBridge
public import Mathlib.Algebra.Polynomial.Eval.Defs

@[expose] public section

namespace RKResearch.Certified.PaidDefectBridge

open RKResearch FiniteRootedTree
open RKResearch.Certified.Graded (row)
open scoped Matrix BigOperators

/-- Four residual scalar entries, indexed by the two pairs of evaluations. -/
structure Moment2 (K : Type*) where
  m00 : K
  m01 : K
  m10 : K
  m11 : K

namespace Moment2

variable {K : Type*}

/-- A literal 2×2 bilinear contraction, with no rank assumptions. -/
def pair [Semiring K] (M : Moment2 K) (a c : Fin 2 → K) : K :=
  (a 0 * M.m00 * c 0 + a 0 * M.m01 * c 1) +
    (a 1 * M.m10 * c 0 + a 1 * M.m11 * c 1)

theorem pair_eq_zero [Semiring K] (M : Moment2 K) (a c : Fin 2 → K)
    (h00 : M.m00 = 0) (h01 : M.m01 = 0) (h10 : M.m10 = 0) (h11 : M.m11 = 0) :
    M.pair a c = 0 := by
  simp only [pair, h00, h01, h10, h11, mul_zero, zero_mul, add_zero]

/-- Once the three allowed tap payments are assigned, this is the leftover form. -/
def oneHole [Ring K] (calibration : K) : Moment2 K :=
  ⟨0, -calibration, 0, 0⟩

theorem pair_oneHole [Ring K] (calibration : K) (a c : Fin 2 → K) :
    (oneHole calibration).pair a c = a 0 * (-calibration) * c 1 := by
  simp [pair, oneHole]

/-- Signed residuals of the three available strict taps and the missing fourth. -/
def ofTaps [Ring K] (W4 W5 s40 s50 s54 l40 l44 l50 l54 : K) : Moment2 K :=
  ⟨W4 * s40 - l40, -l44, W5 * s50 - l50, W5 * s54 - l54⟩

theorem ofTaps_eq_oneHole [Ring K] (W4 W5 s40 s50 s54 l40 l44 l50 l54 : K)
    (h40 : W4 * s40 = l40) (h50 : W5 * s50 = l50) (h54 : W5 * s54 = l54) :
    ofTaps W4 W5 s40 s50 s54 l40 l44 l50 l54 = oneHole l44 := by
  simp only [ofTaps, oneHole, h40, h50, h54, sub_self]

end Moment2

variable {K : Type*} [Field K] {F S : Type*} [Fintype F] [Fintype S]

/-- The actual weighted primitive seed after a permitted suffix word. -/
abbrev payment (A : Matrix (F ⊕ S) (F ⊕ S) K) (w ξ : S → K)
    (t : FiniteRootedTree) (W : List Letter) : K :=
  row w (wordMap (suffixBlock A) ξ W (primitiveSeed A ξ t))

def LowSeedsZero8 (A : Matrix (F ⊕ S) (F ⊕ S) K) (ξ : S → K) : Prop :=
  ∀ t, treeSize t ≤ 3 → primitiveSeed A ξ t = 0

def ShortPayments8 (A : Matrix (F ⊕ S) (F ⊕ S) K) (w ξ : S → K) : Prop :=
  ∀ (t : FiniteRootedTree) (W : List Letter),
    3 < treeSize t → W.length + treeSize t < 8 → W.length < 3 →
    payment A w ξ t W = 0

/-- Exact top payment after the short reverse profile transport has been proved. -/
def TopExpansion8 (A : Matrix (F ⊕ S) (F ⊕ S) K) (w ξ : S → K)
    (fc : FiniteRootedTree → Fin 2 → K) (rc : List Letter → Fin 2 → K)
    (M : Moment2 K) : Prop :=
  ∀ (t : FiniteRootedTree) (W : List Letter), treeSize t = 4 → W.length = 3 →
    payment A w ξ t W = M.pair (fc t) (rc W)

/-- Order eight requires only the short payments and the four top entries. -/
theorem hasOrder_eight_of_moment2 [CharZero K]
    (A : Matrix (F ⊕ S) (F ⊕ S) K) (w ξ : S → K)
    (fc : FiniteRootedTree → Fin 2 → K) (rc : List Letter → Fin 2 → K)
    (M : Moment2 K)
    (hquad : HasQuadratureOrder 8 w ξ) (hlow : LowSeedsZero8 A ξ)
    (hshort : ShortPayments8 A w ξ) (htop : TopExpansion8 A w ξ fc rc M)
    (h00 : M.m00 = 0) (h01 : M.m01 = 0) (h10 : M.m10 = 0) (h11 : M.m11 = 0) :
    HasOrder 8 A (Sum.elim (0 : F → K) w) := by
  apply hasOrder_of_paid_defect_words (p := 8) (q := 3) A w ξ (by decide) hquad
  · intro t ht _
    exact hlow t ht
  · intro t W ht hb
    change payment A w ξ t W = 0
    by_cases hs : W.length < 3
    · exact hshort t W ht hb hs
    · have hn : treeSize t = 4 := by omega
      have hw : W.length = 3 := by omega
      rw [htop t W hn hw]
      exact M.pair_eq_zero (fc t) (rc W) h00 h01 h10 h11

theorem hasOrder_eight_of_oneHole [CharZero K]
    (A : Matrix (F ⊕ S) (F ⊕ S) K) (w ξ : S → K)
    (fc : FiniteRootedTree → Fin 2 → K) (rc : List Letter → Fin 2 → K)
    (calibration : K)
    (hquad : HasQuadratureOrder 8 w ξ) (hlow : LowSeedsZero8 A ξ)
    (hshort : ShortPayments8 A w ξ)
    (htop : TopExpansion8 A w ξ fc rc (Moment2.oneHole calibration))
    (hcal : calibration = 0) :
    HasOrder 8 A (Sum.elim (0 : F → K) w) := by
  refine hasOrder_eight_of_moment2 A w ξ fc rc (Moment2.oneHole calibration)
    hquad hlow hshort htop rfl ?_ rfl rfl
  simp only [Moment2.oneHole, hcal, neg_zero]

/-- Coordinates are actual polynomial evaluations at two supplied locations. -/
noncomputable def polyCoordinates (x : Fin 2 → K) (P : Polynomial K) : Fin 2 → K :=
  fun i => P.eval (x i)

/-- Evaluate the formal word profile minus the projected old-stage profile. -/
noncomputable def reverseCoordinates (y : Fin 2 → K)
    (formalProfile projectedProfile : List Letter → Polynomial K) (W : List Letter) : Fin 2 → K :=
  polyCoordinates y (formalProfile W - projectedProfile W)

/-- Degree-seven beta moments for the cubic pairing, written purely in coefficients.
Application to actual weighted nodes uses cubic bounds and independent exact quadrature. -/
noncomputable def coefficientPairing (γ : K) (H P : Polynomial K) : K :=
  ∑ i : Fin 4, ∑ j : Fin 4,
    H.coeff i.val * P.coeff j.val *
      (Nat.factorial i.val : K) * (Nat.factorial j.val : K) *
        ((Nat.factorial (i.val + j.val + 2) : K)⁻¹ -
          γ * (Nat.factorial (i.val + j.val + 1) : K)⁻¹)

noncomputable def coefficientTapTable (γ W4 W5 s40 s50 s54 : K)
    (H P : Fin 2 → Polynomial K) : Moment2 K :=
  Moment2.ofTaps W4 W5 s40 s50 s54
    (coefficientPairing γ (H 0) (P 0)) (coefficientPairing γ (H 0) (P 1))
    (coefficientPairing γ (H 1) (P 0)) (coefficientPairing γ (H 1) (P 1))

/-- Typed specialization: shorter words and the actual reverse profiles are
inputs, with exact coefficient payments at the three taps and the missing pair. -/
theorem hasOrder_eight_of_coefficient_taps [CharZero K]
    (A : Matrix (F ⊕ S) (F ⊕ S) K) (w ξ : S → K)
    (x y : Fin 2 → K) (forwardDefect : FiniteRootedTree → Polynomial K)
    (formalProfile projectedProfile : List Letter → Polynomial K)
    (H P : Fin 2 → Polynomial K) (γ W4 W5 s40 s50 s54 : K)
    (hquad : HasQuadratureOrder 8 w ξ) (hlow : LowSeedsZero8 A ξ)
    (hshort : ShortPayments8 A w ξ)
    (htop : TopExpansion8 A w ξ (fun t => polyCoordinates x (forwardDefect t))
      (reverseCoordinates y formalProfile projectedProfile) (coefficientTapTable γ W4 W5 s40 s50 s54 H P))
    (h40 : W4 * s40 = coefficientPairing γ (H 0) (P 0))
    (h50 : W5 * s50 = coefficientPairing γ (H 1) (P 0))
    (h54 : W5 * s54 = coefficientPairing γ (H 1) (P 1))
    (h44 : coefficientPairing γ (H 0) (P 1) = 0) :
    HasOrder 8 A (Sum.elim (0 : F → K) w) := by
  have etable :
      coefficientTapTable γ W4 W5 s40 s50 s54 H P =
        Moment2.oneHole (coefficientPairing γ (H 0) (P 1)) := by
    unfold coefficientTapTable
    exact Moment2.ofTaps_eq_oneHole W4 W5 s40 s50 s54
      (coefficientPairing γ (H 0) (P 0)) (coefficientPairing γ (H 0) (P 1))
      (coefficientPairing γ (H 1) (P 0)) (coefficientPairing γ (H 1) (P 1))
      h40 h50 h54
  rw [etable] at htop
  exact hasOrder_eight_of_oneHole A w ξ
    (fun t => polyCoordinates x (forwardDefect t))
    (reverseCoordinates y formalProfile projectedProfile) (coefficientPairing γ (H 0) (P 1))
    hquad hlow hshort htop h44

/-- Optional observer: order can force payment of a word only after an
exact emitted probe identity has separately isolated that payment. -/
theorem payment_zero_of_exact_order8_probe [CharZero K]
    (A : Matrix (F ⊕ S) (F ⊕ S) K) (w ξ : S → K)
    (t probe : FiniteRootedTree) (W : List Letter)
    (horder : HasOrder 8 A (Sum.elim (0 : F → K) w)) (hsize : treeSize probe ≤ 8)
    (hexact :
      (factorialNat probe : K) * ((Sum.elim (0 : F → K) w) ⬝ᵥ Φ probe A) =
        1 + (factorialNat probe : K) * payment A w ξ t W) :
    payment A w ξ t W = 0 := by
  have hresult :
      (factorialNat probe : K) * ((Sum.elim (0 : F → K) w) ⬝ᵥ Φ probe A) = 1 :=
    horder probe hsize
  have e := hexact.symm.trans hresult
  have hz : (factorialNat probe : K) * payment A w ξ t W = 0 :=
    add_left_cancel (e.trans (add_zero (1 : K)).symm)
  have hn : factorialNat probe ≠ 0 := ne_of_gt probe.factorial.pos
  exact (mul_eq_zero.mp hz).resolve_left (Nat.cast_ne_zero.mpr hn)

/-- Conditional necessity for a single remaining coefficient. The two
nonzero evaluated residuals ensure the exact probe observes this entry. -/
theorem calibration_zero_of_exact_order8_probe [CharZero K]
    (A : Matrix (F ⊕ S) (F ⊕ S) K) (w ξ : S → K)
    (fc : FiniteRootedTree → Fin 2 → K) (rc : List Letter → Fin 2 → K)
    (calibration : K)
    (htop : TopExpansion8 A w ξ fc rc (Moment2.oneHole calibration))
    (t probe : FiniteRootedTree) (W : List Letter)
    (ht : treeSize t = 4) (hw : W.length = 3)
    (hnf : fc t 0 ≠ 0) (hnr : rc W 1 ≠ 0)
    (horder : HasOrder 8 A (Sum.elim (0 : F → K) w)) (hsize : treeSize probe ≤ 8)
    (hexact :
      (factorialNat probe : K) * ((Sum.elim (0 : F → K) w) ⬝ᵥ Φ probe A) =
        1 + (factorialNat probe : K) * payment A w ξ t W) :
    calibration = 0 := by
  have hp := payment_zero_of_exact_order8_probe A w ξ t probe W horder hsize hexact
  have h := htop t W ht hw
  rw [Moment2.pair_oneHole] at h
  have hprod : fc t 0 * (-calibration) * rc W 1 = 0 := h.symm.trans hp
  have hleft : fc t 0 * (-calibration) = 0 := (mul_eq_zero.mp hprod).resolve_right hnr
  exact neg_eq_zero.mp ((mul_eq_zero.mp hleft).resolve_left hnf)

end RKResearch.Certified.PaidDefectBridge
