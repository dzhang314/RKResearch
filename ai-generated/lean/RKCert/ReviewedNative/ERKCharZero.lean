module

public import RKCert.ReviewedNative.ERKUniform
public import RKCert.ReviewedNative.ERKGradeFiveSurplus
public import RKCert.ReviewedNative.CoefficientField
public import RKCert.ReviewedNative.TwoSeedRank

public section

/-! # Native characteristic-zero ERK floor from the grade-five surplus

The starting rank five is the published native result. This file carries
any measured rank through a paid midpoint and combines it with the two
physical stage budgets, with no new order-specific geometry or replay.
-/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch Module

variable {K : Type*} [Field K] {s p : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- Any increment beyond rank q at the paid midpoint q = ⌊p/2⌋ pays one
additional stage. This numerical join itself holds over *all* fields. -/
theorem erk_count_of_midpoint_rank (ha : ∀ i j, i ≤ j → A i j=0)
    (ho : HasOrder A b p) (hp : 4≤p) (extra : ℕ)
    (rank : p/2+extra ≤ finrank K (zeroSpace A (p/2))) :
    (3*p+1)/2-1+extra ≤ s := by
  let q := p/2
  by_cases even : p%2=0
  · have room := erk_even_midpoint_budget ha ho (q:=q) (by dsimp [q]; omega)
      (by dsimp [q]; omega)
    dsimp [q] at room
    omega
  · have room := erk_odd_midpoint_budget ha ho (q:=q) (by dsimp [q]; omega)
      (by dsimp [q]; omega)
    dsimp [q] at room
    omega

section CharacteristicZero
variable [CharZero K]

/-- Graded strict growth carries every already earned rank over an
arbitrary subinterval of an actually separated degree. -/
theorem erk_rank_interval_of_coeff_sep (ha : ∀ i j, i ≤ j → A i j=0)
    {a q : ℕ} (ha1 : 1≤a) (le : a≤q)
    (sep : ∀ c, coeffEval A q c ∈ zeroSpace A q → c=0) :
    finrank K (zeroSpace A a)+(q-a) ≤ finrank K (zeroSpace A q) := by
  have g := RKCert.ReviewedNative.RankFlags.finrank_gain_of_steps (zeroSpace A) le
    (fun j hj hq => zeroSpace_strict_of_separation ha sep (by omega) (by omega))
  simpa only [Nat.add_comm] using g

/-- The actual strict first row supplies the origin needed at the even
cutoff 2q. No moment at order 2q+1 is borrowed. -/
theorem erk_paid_rank_interval (ha : ∀ i j, i ≤ j → A i j=0)
    (ho : HasOrder A b p) {a q : ℕ} (ha1 : 1≤a) (le : a≤q) (pay : 2*q≤p) :
    finrank K (zeroSpace A a)+(q-a) ≤ finrank K (zeroSpace A q) := by
  cases s with
  | zero =>
    have chain := RKResearch.Certified.explicit_order_le_stages ha ho
    omega
  | succ s =>
    exact erk_rank_interval_of_coeff_sep ha ha1 le (explicit_coeff_separated ha ho pay)

/-- Every paid midpoint at or beyond grade five retains the one genuine
surplus, computed in the original tableau's defect flag. -/
theorem erk_grade_five_rank_at_paid_midpoint (ha : ∀ i j, i ≤ j → A i j=0)
    (ho : HasOrder A b p) {q : ℕ} (hq : 5≤q) (pay : 2*q≤p) :
    q ≤ finrank K (zeroSpace A q) := by
  have five := grade_five_surplus_of_reviewed_order ha ho (by omega)
  have gain := erk_paid_rank_interval ha ho (a:=5) (by decide) hq pay
  omega

end CharacteristicZero
end RKResearch.Certified.Graded.Reverse

namespace RKResearch
open Certified.Graded.Reverse
universe u v

/-- Strict triangularity and actual rooted-tree order descend to a field
with the same characteristic zero. The original ring may have zero divisors
or additive torsion; a general maximal ideal on it need not preserve the
nonzero integer scalars. -/
theorem HasOrder.strict_lower_triangular_of_charZero_fields
    {ι : Type v} [Fintype ι] [LE ι] {R : Type u} [CommRing R] [CharZero R]
    {A : Matrix ι ι R} {b : ι → R} {p : ℕ} {C : Prop}
    (h : HasOrder A b p) (ha : ∀ i j, i ≤ j → A i j=0)
    (hf : ∀ (K : Type u) [Field K] [CharZero K] (T : Matrix ι ι K) (w : ι → K),
      (∀ i j, i ≤ j → T i j=0) → HasOrder T w p → C) : C :=
  RKCert.ReviewedNative.with_charZero_field (fun K _ _ f =>
    hf K (A.map f) (f ∘ b)
      (fun i j hij => by rw [Matrix.map_apply,ha i j hij,map_zero]) (h.map_coefficients f))

/-- The grade-five enhancement at all orders p ≥ 10 over every
characteristic-zero field. -/
theorem HasOrder.erk_grade_five_charZero_stages_field {K : Type*} [Field K] [CharZero K]
    {s p : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (h : HasOrder A b p) (ha : ∀ i j, i ≤ j → A i j=0) (hp : 10≤p) :
    (3*p+1)/2-1 ≤ s := by
  have r := erk_grade_five_rank_at_paid_midpoint ha h (q:=p/2) (by omega) (by omega)
  simpa only [Nat.add_zero] using erk_count_of_midpoint_rank ha h (by omega) 0 (by simpa using r)

/-- The characteristic-zero ERK grade-five floor, on the original strictly
lower tableau over an arbitrary characteristic-zero commutative ring. -/
theorem HasOrder.erk_grade_five_charZero_stages {R : Type u} [CommRing R] [CharZero R]
    {s p : ℕ} {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (h : HasOrder A b p) (ha : ∀ i j, i ≤ j → A i j=0) (hp : 10≤p) :
    (3*p+1)/2-1 ≤ s :=
  h.strict_lower_triangular_of_charZero_fields ha
    (fun _ _ _ _ _ ht ho => ho.erk_grade_five_charZero_stages_field ht hp)

end RKResearch
