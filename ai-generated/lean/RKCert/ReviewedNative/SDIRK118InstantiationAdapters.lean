module

public import RKCert.ReviewedNative.SDIRK118ChartGlue
public import Mathlib.Data.Real.Basic

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKResearch.Certified.PaidDefectBridge.ChartInstantiation

open RKResearch RKResearch.FiniteRootedTree
open RKResearch.Certified.PaidDefectBridge (Letter wordMap)
open scoped Matrix FiniteRootedTree BigOperators

variable {K : Type*} [Field K]

/-- Coordinate covector for both literal donor frames and the suffix rows. -/
def coordinate {ι : Type*} (i : ι) : (ι → K) →ₗ[K] K where
  toFun v := v i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section Restriction

variable {J I : Type*} [Fintype J] [Fintype I]

/-- A coordinate restriction preserving matrix action preserves reviewed Φ,
even for nonzero diagonals. -/
theorem phi_comp_of_mulVec
    (A : Matrix I I K) (B : Matrix J J K) (r : J → I)
    (h : ∀ v : I → K, (A *ᵥ v) ∘ r = B *ᵥ (v ∘ r))
    (t : FiniteRootedTree) : Φ t A ∘ r = Φ t B := by
  induction t with
  | leaf => rfl
  | butcherProduct u v hu hv =>
    change (Φ u A ∘ r) * ((A *ᵥ Φ v A) ∘ r) = Φ u B * (B *ᵥ Φ v B)
    rw [hu, h, hv]

/-- The same restriction preserves every actual word when the clock also
restricts. Head/outermost orientation agrees with the checked wordMap. -/
theorem wordMap_comp_of_mulVec_clock
    (A : Matrix I I K) (B : Matrix J J K) (r : J → I)
    (ξ : I → K) (ζ : J → K)
    (h : ∀ v : I → K, (A *ᵥ v) ∘ r = B *ᵥ (v ∘ r))
    (hc : ξ ∘ r = ζ) (W : List Letter) (v : I → K) :
    wordMap A ξ W v ∘ r = wordMap B ζ W (v ∘ r) := by
  induction W with
  | nil => rfl
  | cons l W ih =>
    cases l
    · change (A *ᵥ wordMap A ξ W v) ∘ r = B *ᵥ wordMap B ζ W (v ∘ r)
      rw [h, ih]
    · change (ξ ∘ r) * (wordMap A ξ W v ∘ r) = ζ * wordMap B ζ W (v ∘ r)
      rw [hc, ih]

end Restriction

/-- The only prefix block premise is a zero upper-right block. -/
theorem mulVec_inl_of_upperRight_zero
    {F S : Type*} [Fintype F] [Fintype S]
    (A : Matrix (F ⊕ S) (F ⊕ S) K) (G : Matrix F F K)
    (hG : ∀ i j, A (Sum.inl i) (Sum.inl j) = G i j)
    (h0 : ∀ i j, A (Sum.inl i) (Sum.inr j) = 0)
    (v : F ⊕ S → K) : (A *ᵥ v) ∘ Sum.inl = G *ᵥ (v ∘ Sum.inl) := by
  funext i
  change (∑ j : F ⊕ S, A (Sum.inl i) j * v j) =
    ∑ j : F, G i j * v (Sum.inl j)
  rw [Fintype.sum_sum_type]
  simp only [hG, h0, zero_mul, Finset.sum_const_zero, add_zero]

section LowShapes

abbrev t1 : FiniteRootedTree := .leaf
abbrev t2 : FiniteRootedTree := t1 ◂ t1
abbrev t3a : FiniteRootedTree := t2 ◂ t1
abbrev t3b : FiniteRootedTree := t1 ◂ t2

private theorem size_join (u v : FiniteRootedTree) :
    treeSize (u ◂ v) = treeSize u + treeSize v := by
  simp only [treeSize, FiniteRootedTree.order, PNat.add_coe]

private theorem size_one_eq (t : FiniteRootedTree) (h : treeSize t = 1) :
    t = t1 := by
  cases t with
  | leaf => rfl
  | butcherProduct u v =>
    have hu : 0 < treeSize u := u.order.pos
    have hv : 0 < treeSize v := v.order.pos
    have hs := (size_join u v).symm.trans h
    omega

private theorem size_two_eq (t : FiniteRootedTree) (h : treeSize t = 2) :
    t = t2 := by
  cases t with
  | leaf =>
    change (1 : ℕ) = 2 at h
    omega
  | butcherProduct u v =>
    have hu : 0 < treeSize u := u.order.pos
    have hv : 0 < treeSize v := v.order.pos
    have hs := (size_join u v).symm.trans h
    rw [size_one_eq u (by omega), size_one_eq v (by omega)]

private theorem size_three_eq (t : FiniteRootedTree) (h : treeSize t = 3) :
    t = t3a ∨ t = t3b := by
  cases t with
  | leaf =>
    change (1 : ℕ) = 3 at h
    omega
  | butcherProduct u v =>
    have hu : 0 < treeSize u := u.order.pos
    have hv : 0 < treeSize v := v.order.pos
    have hs := (size_join u v).symm.trans h
    by_cases hl : treeSize u = 1
    · exact Or.inr (by rw [size_one_eq u hl, size_two_eq v (by omega)])
    · exact Or.inl (by rw [size_two_eq u (by omega), size_one_eq v (by omega)])

private theorem size_four_eq (t : FiniteRootedTree) (h : treeSize t = 4) :
    t = (t3a ◂ t1) ∨ t = (t3b ◂ t1) ∨ t = (t2 ◂ t2) ∨
    t = (t1 ◂ t3a) ∨ t = (t1 ◂ t3b) := by
  cases t with
  | leaf =>
    change (1 : ℕ) = 4 at h
    omega
  | butcherProduct u v =>
    have hu : 0 < treeSize u := u.order.pos
    have hv : 0 < treeSize v := v.order.pos
    have hs := (size_join u v).symm.trans h
    by_cases hl : treeSize u = 1
    · have eu := size_one_eq u hl
      rcases size_three_eq v (by omega) with ev | ev
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [eu, ev]))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by rw [eu, ev]))))
    · by_cases hm : treeSize u = 2
      · exact Or.inr (Or.inr (Or.inl (by rw [size_two_eq u hm, size_two_eq v (by omega)])))
      · have ev := size_one_eq v (by omega)
        rcases size_three_eq u (by omega) with eu | eu
        · exact Or.inl (by rw [eu, ev])
        · exact Or.inr (Or.inl (by rw [eu, ev]))

/-- Discharge arbitrary reviewed low/grade-three tree statements by the
actual constructor shapes. No new tree type or canonical quotient. -/
theorem tree_gates_of_small_shapes (Low Top : FiniteRootedTree → Prop)
    (hl1 : Low t1) (hl2 : Low t2) (hl3a : Low t3a) (hl3b : Low t3b)
    (ha : Top (t3a ◂ t1)) (hb : Top (t3b ◂ t1)) (hc : Top (t2 ◂ t2))
    (hd : Top (t1 ◂ t3a)) (he : Top (t1 ◂ t3b)) :
    (∀ t, treeSize t ≤ 3 → Low t) ∧ (∀ t, treeSize t = 4 → Top t) := by
  constructor
  · intro t ht
    have hp : 0 < treeSize t := t.order.pos
    by_cases h1 : treeSize t = 1
    · simpa only [size_one_eq t h1] using hl1
    · by_cases h2 : treeSize t = 2
      · simpa only [size_two_eq t h2] using hl2
      · rcases size_three_eq t (by omega) with h | h
        · simpa only [h] using hl3a
        · simpa only [h] using hl3b
  · intro t ht
    rcases size_four_eq t ht with h | h | h | h | h
    · simpa only [h] using ha
    · simpa only [h] using hb
    · simpa only [h] using hc
    · simpa only [h] using hd
    · simpa only [h] using he

/-- Proof interface for the nil, one-letter and two-letter low tables. -/
theorem word_gate_le_two {L : Type*} (Q : List L → Prop) (hnil : Q [])
    (h1 : ∀ a, Q [a]) (h2 : ∀ a b, Q [a,b]) :
    ∀ W, W.length ≤ 2 → Q W := by
  intro W h
  cases W with
  | nil => exact hnil
  | cons a W =>
    cases W with
    | nil => exact h1 a
    | cons b W =>
      cases W with
      | nil => exact h2 a b
      | cons c W =>
        simp only [List.length_cons] at h
        omega

theorem word_gate_three {L : Type*} (Q : List L → Prop)
    (step : ∀ a U, U.length = 2 → Q (a :: U)) :
    ∀ W, W.length = 3 → Q W := by
  intro W h
  cases W with
  | nil =>
    simp only [List.length_nil] at h
    omega
  | cons a U =>
    apply step a U
    simp only [List.length_cons] at h
    omega

end LowShapes

/-- Exact affine calibration, using the unscaled signs in their native
orientation. Nonzero and the actual zero both follow from the bracket. -/
theorem affine_ratio_of_bracket {a b l u : ℝ}
    (hlu : l < u) (hl : a*l+b < 0) (hu : 0 < a*u+b) :
    0 < a ∧ l < -b/a ∧ -b/a < u ∧ a*(-b/a)+b = 0 := by
  have hdiff : 0 < (a*u+b) - (a*l+b) := sub_pos.mpr (hl.trans hu)
  have hprod : 0 < a * (u-l) := by
    convert hdiff using 1 <;> ring
  have ha : 0 < a := by
    by_contra hn
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg
      (le_of_not_gt hn) (sub_nonneg.mpr hlu.le))) hprod
  refine ⟨ha, (lt_div_iff₀ ha).2 ?_, (div_lt_iff₀ ha).2 ?_, ?_⟩
  · nlinarith only [hl]
  · nlinarith only [hu]
  · calc
      a * (-b/a) + b = (-b/a) * a + b := by rw [mul_comm a]
      _ = 0 := by rw [div_mul_cancel₀ _ (ne_of_gt ha), neg_add_cancel]

end RKResearch.Certified.PaidDefectBridge.ChartInstantiation
