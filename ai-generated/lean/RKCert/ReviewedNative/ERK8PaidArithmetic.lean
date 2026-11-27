module

public import RKCert.ReviewedNative.ERK8PaidCensus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Bounded factorial-unit arithmetic, with no characteristic assumption -/
namespace RKResearch.Certified.Graded.OneOff.PaidProof

open RKResearch FiniteRootedTree
open scoped Matrix

/-- Internal consumer capability. The literal reviewed order-eight
predicate pays it; it is not a hypothesis of the final exclusion. -/
class EightUnits (K : Type*) [CommRing K] : Prop where
  unit : IsUnit ((Nat.factorial 8 : ℕ) : K)

theorem eightUnits_of_order {K : Type*} [CommRing K] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K} (ho : HasOrder 8 A b) :
    EightUnits K := by
  constructor
  have h := ho (tallTree 8) (by decide)
  have e : ((tallTree 8).factorial:K)=((Nat.factorial 8:ℕ):K) := by norm_cast
  exact IsUnit.of_mul_eq_one _ (e ▸ h)

theorem paidCastUnit {K : Type*} [CommRing K] [EightUnits K] (n : ℕ)
    (h : n∣(Nat.factorial 8)^5) : IsUnit (n:K) := by
  apply isUnit_of_dvd_unit (Nat.cast_dvd_cast (α:=K) h)
  simpa only [Nat.cast_pow] using (EightUnits.unit (K:=K)).pow 5

theorem paidCastNe {K : Type*} [CommRing K] [Nontrivial K] [EightUnits K] (n : ℕ)
    (h : n∣(Nat.factorial 8)^5) : (n:K)≠0 :=
  (paidCastUnit n h).ne_zero

theorem lowCastUnit {K : Type*} [CommRing K] [EightUnits K] (n : ℕ)
    (pos : 0<n) (le : n≤8) : IsUnit (n:K) :=
  isUnit_of_dvd_unit (Nat.cast_dvd_cast (α:=K) (Nat.dvd_factorial pos le))
    (EightUnits.unit (K:=K))

theorem two_paid (K : Type*) [Field K] [EightUnits K] : (2:K)≠0 := paidCastNe 2 (by decide)
theorem three_paid (K : Type*) [Field K] [EightUnits K] : (3:K)≠0 := paidCastNe 3 (by decide)
theorem four_paid (K : Type*) [Field K] [EightUnits K] : (4:K)≠0 := paidCastNe 4 (by decide)
theorem five_paid (K : Type*) [Field K] [EightUnits K] : (5:K)≠0 := paidCastNe 5 (by decide)
theorem six_paid (K : Type*) [Field K] [EightUnits K] : (6:K)≠0 := paidCastNe 6 (by decide)
theorem seven_paid (K : Type*) [Field K] [EightUnits K] : (7:K)≠0 := paidCastNe 7 (by decide)
theorem eight_paid (K : Type*) [Field K] [EightUnits K] : (8:K)≠0 := paidCastNe 8 (by decide)
theorem nine_paid (K : Type*) [Field K] [EightUnits K] : (9:K)≠0 := paidCastNe 9 (by decide)
theorem twelve_paid (K : Type*) [Field K] [EightUnits K] : (12:K)≠0 := paidCastNe 12 (by decide)
theorem fourteen_paid (K : Type*) [Field K] [EightUnits K] : (14:K)≠0 := paidCastNe 14 (by decide)
theorem thirtyTwo_paid (K : Type*) [Field K] [EightUnits K] : (32:K)≠0 := paidCastNe 32 (by decide)

theorem mat_zeroSpace_bounded {K : Type*} [Field K] [EightUnits K]
    {ι : Type*} [Fintype ι] (A : Matrix ι ι K) (j : ℕ)
    {v : ι→K} (m : v∈zeroSpace A j) (bound : j+1≤8 := by omega) :
    mat A v∈zeroSpace A (j+1) :=
  mat_zeroSpace_of_unit A j (fun t h=>lowCastUnit _ t.order.pos (h.trans bound)) m

/-- Presentation tactics for the bounded arithmetic. Their proof terms
only use explicit numeral receipts and standard field normalization. -/
macro "eight_num" : tactic =>
  `(tactic| first
    | (norm_num; done)
    | (apply paidCastNe; decide)
    | (norm_num; apply paidCastNe; decide)
    | (apply div_ne_zero <;> (apply paidCastNe; decide)))

macro "eight_ring" K:term : tactic =>
  `(tactic| first
    | ring1
    | (field_simp [two_paid $K,three_paid $K,four_paid $K,five_paid $K,six_paid $K,
        seven_paid $K,eight_paid $K,nine_paid $K,twelve_paid $K,fourteen_paid $K,thirtyTwo_paid $K] <;> ring1))

theorem zeroSpace_strict_paid8 {K : Type*} [Field K] [EightUnits K] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) K} (strict : ∀ i j, i≤j→A i j=0)
    {q j : ℕ} (sep : ∀ a,coeffEval A q a∈zeroSpace A q→a=0)
    (jpos : 1≤j) (jq : j+1≤q) (bj : j+1≤8 := by omega) :
    zeroSpace A j<zeroSpace A (j+1) := by
  refine lt_of_le_of_ne (zeroSpace_mono A (Nat.le_succ _)) ?_
  intro h
  apply nodes_not_defect_of_separation (by omega) sep
  apply zeroSpace_mono A jq
  rw [←h,←show diag (nodes A) (1:Fin s→K)=nodes A by ext i; simp]
  apply mem_of_invariant_seed (Equiv.refl _) (mat A) (causal_mat strict) (nodes A) 1 (zeroSpace A j)
  · intro v hv
    rw [h]
    exact mat_zeroSpace_bounded A j hv bj
  · intro v hv
    rw [h]
    exact diag_zeroSpace A j hv
  · rw [h]
    exact zeroSpace_mono A (by omega) (forward_seed_mem A)

end RKResearch.Certified.Graded.OneOff.PaidProof

#print axioms RKResearch.Certified.Graded.OneOff.PaidProof.eightUnits_of_order
#print axioms RKResearch.Certified.Graded.OneOff.PaidProof.mat_zeroSpace_bounded
