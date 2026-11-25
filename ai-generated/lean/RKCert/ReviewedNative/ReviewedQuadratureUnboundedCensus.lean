module

public import RKCert.ReviewedNative.FormalSignedQuadrature
public import RKCert.ReviewedNative.EffectiveDonorClocks
import RKCert.ReviewedNative.OrderedNodalGain
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKResearch.Certified.Graded.SignedQuadrature

open RKResearch Polynomial
open RKResearch.Certified.Graded.EffectiveDonors
open RKCert.ReviewedNative.UnitBetaSquareMass RKCert.ReviewedNative.FormalSignedQuadrature
open scoped BigOperators Classical Matrix

noncomputable section
variable {K ι : Type*} [Field K] [Fintype ι]

/-- All genuine nonzero aggregate masses. In contrast to the shifted
effective donor set, this also retains an active clock zero. -/
def activeAggregates (c w : ι → K) : Finset K :=
  (Finset.univ.image c).filter (fun x => clockMass c w x ≠ 0)

theorem activeAggregates_mass_ne_zero {c w : ι → K} {x : K}
    (h : x ∈ activeAggregates c w) : clockMass c w x ≠ 0 :=
  (Finset.mem_filter.mp h).2

theorem activeAggregates_card_le (c w : ι → K) :
    (activeAggregates c w).card ≤ Fintype.card ι := by
  classical
  calc
    (activeAggregates c w).card ≤ (Finset.univ.image c).card := Finset.card_filter_le _ _
    _ ≤ (Finset.univ : Finset ι).card := Finset.card_image_le
    _ = _ := Finset.card_univ

private theorem aggregate_sum (c w : ι → K) (H : K[X]) :
    (∑ i, w i*H.eval (c i)) =
      ∑ x ∈ activeAggregates c w, clockMass c w x*H.eval x := by
  classical
  let U : Finset K := Finset.univ.image c
  calc
    _ = ∑ x ∈ U, ∑ i ∈ Finset.univ.filter (fun i => c i=x),
          w i*H.eval (c i) :=
      (Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := U) (g := c)
        (fun i hi => Finset.mem_image_of_mem c hi)
        (fun i => w i*H.eval (c i))).symm
    _ = ∑ x ∈ U, clockMass c w x*H.eval x := by
      apply Finset.sum_congr rfl
      intro x _
      have wnet : clockMass c w x = ∑ i ∈ Finset.univ.filter (fun i => c i=x), w i := by
        simp only [clockMass, Finset.sum_filter]
      rw [wnet, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := by
      have sub : activeAggregates c w ⊆ U := Finset.filter_subset _ _
      symm
      apply Finset.sum_subset sub
      intro x hx off
      have z : clockMass c w x = 0 := by
        by_contra nz
        exact off (Finset.mem_filter.mpr ⟨hx, nz⟩)
      rw [z, zero_mul]

section Paid
variable [CharZero K]

/-- Native shift-zero polynomial payment, grouped without changing the tableau. -/
theorem unit_law {p : ℕ} {A : Matrix ι ι K} {w : ι → K}
    (ho : HasOrder p A w) (p0 : 0 < p) :
    UnitLaw (activeAggregates (nodes A) w) (clockMass (nodes A) w) (p-1) := by
  intro H hd
  have h := probe_evalNodes ho H 0 (by omega)
  have exactPay : mass H = ∑ i, w i*H.eval (nodes A i) := by
    rw [mass_apply, formalPrimitive_eq_native]
    simpa only [probe, row_apply, dotProduct, pow_zero, mul_one, evalNodes_apply,
      one_mul] using h.symm
  exact exactPay.trans (aggregate_sum (nodes A) w H)

end Paid

section Ordered
variable [LinearOrder K] [IsStrictOrderedRing K]

theorem order_le_twice_positive_aggregates {p : ℕ} {A : Matrix ι ι K} {w : ι → K}
    (ho : HasOrder p A w) :
    p ≤ 2*((activeAggregates (nodes A) w).filter (fun x => 0 < clockMass (nodes A) w x)).card := by
  by_cases hp : p=0
  · simp only [hp, Nat.zero_le]
  have ppos : 0 < p := Nat.pos_of_ne_zero hp
  have raw := (unit_law ho ppos).positive_budget
  omega

theorem order_plus_exterior_and_negative_interior {p : ℕ}
    {A : Matrix ι ι K} {w : ι → K} (ho : HasOrder p A w) :
    let T := activeAggregates (nodes A) w
    let mu := clockMass (nodes A) w
    p+(exteriorSites T).card+2*(negativeInteriorSites T mu).card≤2*T.card := by
  let T := activeAggregates (nodes A) w
  let mu := clockMass (nodes A) w
  change p+(exteriorSites T).card+2*(negativeInteriorSites T mu).card≤2*T.card
  by_cases hp : p=0
  · simpa only [hp, zero_add] using exterior_negative_le_twice_card T mu
  have ppos : 0 < p := Nat.pos_of_ne_zero hp
  have raw := (unit_law ho ppos).exterior_and_negative_budget
  change p-1+1+(exteriorSites T).card+2*(negativeInteriorSites T mu).card≤2*T.card at raw
  omega

theorem order_plus_exterior_and_negative_interior_le_twice_stages {p : ℕ}
    {A : Matrix ι ι K} {w : ι → K} (ho : HasOrder p A w) :
    let T := activeAggregates (nodes A) w
    let mu := clockMass (nodes A) w
    p+(exteriorSites T).card+2*(negativeInteriorSites T mu).card≤2*Fintype.card ι :=
  (order_plus_exterior_and_negative_interior ho).trans
    (Nat.mul_le_mul_left 2 (activeAggregates_card_le (nodes A) w))

end Ordered
end
end RKResearch.Certified.Graded.SignedQuadrature
