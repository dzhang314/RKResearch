module

public import RKCert.ReviewedNative.Explicit
public import RKCert.ReviewedNative.ChangeCoefficients
public import RKCert.ReviewedNative.GradedGrowth
public import RKCert.ReviewedNative.EndpointAdjoint

public section

/-! # Uniform explicit Runge–Kutta lower bound on the reviewed trees

All counts refer to the original chronological tableau. The even midpoint
uses the actual zero first row to detect the constant clock coefficient.
The odd midpoint includes the paid last-live coordinate or the nonzero
initial reverse seed, but not both. Admissible positive characteristics,
zero weights and repeated nodes are allowed throughout.
-/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch Module

variable {K : Type*} [Field K] {s p : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- At a paid explicit midpoint the true tree-space rank is exactly the
clock rank plus the actual defect rank, even at p = 2q. -/
theorem erk_midpoint_tree_rank (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder p A b) {q : ℕ} (hq : 1 ≤ q) (pay : 2*q ≤ p) :
    finrank K (treeSpace A q) = q+1+finrank K (zeroSpace A q) := by
  cases s with
  | zero =>
    have chain := RKResearch.Certified.explicit_order_le_stages ha ho
    omega
  | succ s =>
    exact explicit_midpoint_rank_eq ha ho (by omega) pay

/-- The measured even-midpoint budget retains the initial reverse rank and
every actual forward surplus. It does not require a live terminal weight. -/
theorem erk_even_midpoint_budget (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder p A b) {q : ℕ} (hq : 2 ≤ q) (pay : 2*q ≤ p) :
    2*q-1+finrank K (zeroSpace A q)+finrank K (back A b 0) ≤ s := by
  have front := erk_midpoint_tree_rank ha ho (by omega) pay
  have rear := backward_count ha ho q (q-2) (by omega)
  omega

/-- The last-live-coordinate refund or the nonzero initial reverse row
pays the same extra dimension at an odd midpoint. Arbitrary actual forward
surplus persists in the bound. -/
theorem erk_odd_midpoint_budget (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder p A b) {q : ℕ} (hq : 1 ≤ q) (pay : 2*q+1 ≤ p) :
    2*q+1+finrank K (zeroSpace A q) ≤ s := by
  have front := erk_midpoint_tree_rank ha ho hq (by omega)
  have rear := backward_endpoint_count ha ho q (q-1) pay (by omega)
  omega

/-- Even order 2q needs at least 3q−2 stages, keeping any initial reverse
seed rank. -/
theorem erk_even_midpoint_floor (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder p A b) {q : ℕ} (hq : 2 ≤ q) (pay : 2*q ≤ p) :
    3*q-2+finrank K (back A b 0) ≤ s := by
  have front := zeroSpace_finrank ha ho (n:=q-1) (by omega)
  rw [show q-1+1=q by omega] at front
  have both := erk_even_midpoint_budget ha ho hq pay
  omega

end RKResearch.Certified.Graded.Reverse

namespace RKResearch
open Module Certified.Graded Certified.Graded.Reverse
universe u v

/-- Strict lower triangularity, including the entire diagonal, is preserved
when specializing the native order conditions through a maximal ideal. -/
theorem HasOrder.strict_lower_triangular_of_all_fields
    {ι : Type v} [Fintype ι] [LE ι] {R : Type u} [CommRing R] [Nontrivial R]
    {A : Matrix ι ι R} {b : ι → R} {p : ℕ} {C : Prop}
    (h : HasOrder p A b) (ha : ∀ i j, i ≤ j → A i j=0)
    (hf : ∀ (K : Type u) [Field K] (T : Matrix ι ι K) (w : ι → K),
      (∀ i j, i ≤ j → T i j=0) → HasOrder p T w → C) : C := by
  obtain ⟨I,hI⟩ := Ideal.exists_maximal R
  let _ := hI
  let _ := Ideal.Quotient.field I
  let f := Ideal.Quotient.mk I
  exact hf (R ⧸ I) (A.map f) (f ∘ b)
    (fun i j hij => by rw [Matrix.map_apply, ha i j hij, map_zero])
    (h.map f)

/-- General field-level explicit lower bound. Paid order ensures the
denominators used in the proof are units; the field need not have
characteristic zero. -/
theorem HasOrder.erk_uniform_stages_field {K : Type*} [Field K] {s p : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (h : HasOrder p A b) (ha : ∀ i j, i ≤ j → A i j=0) :
    max p ((3*p+1)/2-2) ≤ s := by
  have chain := Certified.explicit_order_le_stages ha h
  refine max_le chain ?_
  by_cases small : p ≤ 4
  · omega
  let q := p/2
  have q2 : 2 ≤ q := by dsimp [q]; omega
  have front := zeroSpace_finrank ha h (n:=q-1) (by dsimp [q]; omega)
  rw [show q-1+1=q by omega] at front
  by_cases even : p%2=0
  · have both := erk_even_midpoint_floor ha h q2 (by dsimp [q]; omega)
    dsimp [q] at *
    omega
  · have both := erk_odd_midpoint_budget ha h (q:=q) (by omega) (by dsimp [q]; omega)
    dsimp [q] at *
    omega

/-- Over any nontrivial commutative ring, a strictly lower triangular
order-p tableau needs at least max(p, ⌈3p/2⌉−2) original stages. -/
theorem HasOrder.erk_uniform_stages {R : Type u} [CommRing R] [Nontrivial R] {s p : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (h : HasOrder p A b) (ha : ∀ i j, i ≤ j → A i j=0) :
    max p ((3*p+1)/2-2) ≤ s :=
  h.strict_lower_triangular_of_all_fields ha
    (fun _ _ _ _ ht ord => ord.erk_uniform_stages_field ht)

/-- General explicit-method lower-bound ledger. The entries are necessary
stage counts, not existence claims. -/
def erkUniformFloor (p : ℕ) : ℕ := max p ((3*p+1)/2-2)

theorem HasOrder.erk_uniform_floor_le_stages {R : Type u} [CommRing R] [Nontrivial R] {s p : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (h : HasOrder p A b) (ha : ∀ i j, i ≤ j → A i j=0) :
    erkUniformFloor p ≤ s :=
  h.erk_uniform_stages ha

/-- Regression on the complete published arbitrary-ring explicit column,
with zero-order prepended. -/
theorem erkUniformFloor_through_twenty : (List.range 21).map erkUniformFloor =
    [0,1,2,3,4,6,7,9,10,12,13,15,16,18,19,21,22,24,25,27,28] := by decide

end RKResearch
