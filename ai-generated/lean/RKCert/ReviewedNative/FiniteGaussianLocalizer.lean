module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.LinearAlgebra.Lagrange

import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Finite Gaussian node comparison by a signed localizer

A strict sign count survives weak domination of the localized square form.
A single nodal separator replaces the dimension argument. The mesh and
the two exact rules may be any finite rules over an ordered field.
-/
namespace RKCert.ReviewedNative.FiniteGaussianLocalizer

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

/-- The atomic quadratic form with the signed polynomial localizer \(g\). -/
def signedLocalizer (s : Finset K) (mass : K → K) (g P : K[X]) : K :=
  ∑ x ∈ s, mass x * (g.eval x * (P.eval x)^2)

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- A weak comparison on squares transfers the number of negative nodes.
The reference mass only has to be positive at its negative nodes. Nodes
where the localizer vanishes are not counted in either rule. -/
theorem card_negative_le_of_localizer_le
    {s₀ s₁ : Finset K} {μ₀ μ₁ : K → K} {g : K[X]} {d : ℕ} {c : K}
    (room : s₀.card ≤ d + 1)
    (mass₀ : ∀ x ∈ s₀, g.eval x < 0 → 0 < μ₀ x)
    (mass₁ : ∀ x ∈ s₁, 0 ≤ μ₁ x) (hc : 0 < c)
    (dom : ∀ P : K[X], P.natDegree ≤ d →
      signedLocalizer s₁ μ₁ g P ≤ c * signedLocalizer s₀ μ₀ g P) :
    (s₀.filter (fun x => g.eval x < 0)).card ≤
      (s₁.filter (fun x => g.eval x < 0)).card := by
  let B₀ := s₀.filter (fun x => g.eval x < 0)
  let B₁ := s₁.filter (fun x => g.eval x < 0)
  let C₀ := s₀.filter (fun x => ¬ g.eval x < 0)
  change B₀.card ≤ B₁.card
  by_contra h
  have fewer : B₁.card < B₀.card := Nat.lt_of_not_ge h
  obtain ⟨x, hx₀, hx₁⟩ := Finset.exists_mem_notMem_of_card_lt_card fewer
  have hxmem : x ∈ s₀ := (Finset.mem_filter.mp hx₀).1
  have hxneg : g.eval x < 0 := (Finset.mem_filter.mp hx₀).2
  let U := B₁ ∪ C₀
  let P : K[X] := Lagrange.nodal U id
  have partition : B₀.card + C₀.card = s₀.card :=
    Finset.card_filter_add_card_filter_not (s := s₀) (fun y => g.eval y < 0)
  have ucard : U.card ≤ B₁.card + C₀.card := Finset.card_union_le _ _
  have pd : P.natDegree ≤ d := by
    change (Lagrange.nodal U id).natDegree ≤ d
    rw [Lagrange.natDegree_nodal]
    omega
  have xout : x ∉ U := by
    intro hx
    rcases Finset.mem_union.mp hx with hb | hc₀
    · exact hx₁ hb
    · exact (Finset.mem_filter.mp hc₀).2 hxneg
  have live : P.eval x ≠ 0 := by
    change (Lagrange.nodal U id).eval x ≠ 0
    apply Lagrange.eval_nodal_not_at_node
    intro y hy hxy
    change x = y at hxy
    subst y
    exact xout hy
  have kill (y : K) (hy : y ∈ U) : P.eval y = 0 :=
    Lagrange.eval_nodal_at_node (v := id) hy
  have ref_le (y : K) (hy : y ∈ s₀) :
      μ₀ y * (g.eval y * (P.eval y)^2) ≤ 0 := by
    by_cases hn : g.eval y < 0
    · exact mul_nonpos_of_nonneg_of_nonpos (mass₀ y hy hn).le
        (mul_nonpos_of_nonpos_of_nonneg hn.le (sq_nonneg _))
    · have hC : y ∈ C₀ := Finset.mem_filter.mpr ⟨hy, hn⟩
      simp [kill y (Finset.mem_union.mpr (Or.inr hC))]
  have ref_strict : μ₀ x * (g.eval x * (P.eval x)^2) < 0 :=
    mul_neg_of_pos_of_neg (mass₀ x hxmem hxneg)
      (mul_neg_of_neg_of_pos hxneg (sq_pos_of_ne_zero live))
  have ref_neg : signedLocalizer s₀ μ₀ g P < 0 := by
    have hs :
        (∑ y ∈ s₀, μ₀ y * (g.eval y * (P.eval y)^2)) < ∑ _y ∈ s₀, (0 : K) :=
      Finset.sum_lt_sum ref_le ⟨x, hxmem, ref_strict⟩
    simpa [signedLocalizer] using hs
  have cand_nonneg : 0 ≤ signedLocalizer s₁ μ₁ g P := by
    unfold signedLocalizer
    apply Finset.sum_nonneg
    intro y hy
    by_cases hn : g.eval y < 0
    · have hB : y ∈ B₁ := Finset.mem_filter.mpr ⟨hy, hn⟩
      simp [kill y (Finset.mem_union.mpr (Or.inl hB))]
    · exact mul_nonneg (mass₁ y hy) (mul_nonneg (le_of_not_gt hn) (sq_nonneg _))
  exact (not_lt_of_ge cand_nonneg) ((dom P pd).trans_lt (mul_neg_of_pos_of_neg hc ref_neg))

/-- Exact rules on a common finite mesh. The mesh weights here already
include their respective density factors. The sole comparison hypothesis
is the signed pointwise crossing at the localizer; a global monotonicity
or division hypothesis is unnecessary. The exact test cost is
\(\deg g+2d\). -/
theorem card_negative_le_of_exact_mesh
    {ι : Type*} {s₀ s₁ : Finset K} {μ₀ μ₁ : K → K}
    {g : K[X]} {d : ℕ} {c : K}
    (mesh : Finset ι) (x : ι → K) (w₀ w₁ : ι → K)
    (room : s₀.card ≤ d + 1)
    (mass₀ : ∀ y ∈ s₀, g.eval y < 0 → 0 < μ₀ y)
    (mass₁ : ∀ y ∈ s₁, 0 ≤ μ₁ y) (hc : 0 < c)
    (exact₀ : ∀ Q : K[X], Q.natDegree ≤ g.natDegree + 2 * d →
      (∑ y ∈ s₀, μ₀ y * Q.eval y) = ∑ i ∈ mesh, w₀ i * Q.eval (x i))
    (exact₁ : ∀ Q : K[X], Q.natDegree ≤ g.natDegree + 2 * d →
      (∑ y ∈ s₁, μ₁ y * Q.eval y) = ∑ i ∈ mesh, w₁ i * Q.eval (x i))
    (crossing : ∀ i ∈ mesh, (w₁ i - c * w₀ i) * g.eval (x i) ≤ 0) :
    (s₀.filter (fun y => g.eval y < 0)).card ≤
      (s₁.filter (fun y => g.eval y < 0)).card := by
  apply card_negative_le_of_localizer_le room mass₀ mass₁ hc
  intro P pd
  let Q : K[X] := g * P^2
  have qd : Q.natDegree ≤ g.natDegree + 2 * d :=
    natDegree_mul_le_of_le (p := g) (q := P^2) (le_refl _) (natDegree_pow_le_of_le 2 pd)
  have qe (y : K) : Q.eval y = g.eval y * (P.eval y)^2 := by
    simp only [Q, eval_mul, eval_pow]
  calc
    signedLocalizer s₁ μ₁ g P = ∑ i ∈ mesh, w₁ i * Q.eval (x i) := by
      rw [← exact₁ Q qd]
      simp only [signedLocalizer, qe]
    _ ≤ ∑ i ∈ mesh, c * (w₀ i * Q.eval (x i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have qle : (w₁ i - c * w₀ i) * g.eval (x i) * (P.eval (x i))^2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (crossing i hi) (sq_nonneg _)
      rw [mul_assoc, ← qe (x i), sub_mul] at qle
      exact sub_nonpos.mp (by simpa only [mul_assoc] using qle)
    _ = c * signedLocalizer s₀ μ₀ g P := by
      rw [← Finset.mul_sum, ← exact₀ Q qd]
      simp only [signedLocalizer, qe]

end RKCert.ReviewedNative.FiniteGaussianLocalizer