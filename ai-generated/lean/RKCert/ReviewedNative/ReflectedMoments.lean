module

public import RKCert.ReviewedNative.GradedColumns
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

public section

/-! # Exact reverse moments on the reviewed trees

The reflected powers satisfy the adjacent beta-moment relation purely by
the identity `c^r*(1-c)^(k+1) = c^r*(1-c)^k - c^(r+1)*(1-c)^k`,
the paid forward monomials, and induction. Thus
the familiar D(1), D(2), D(3) balance, and its paid higher-degree instances,
all hold directly on the native tableau without a coefficient field. -/

namespace RKResearch.Certified.Graded

open RKResearch FiniteRootedTree
open scoped Matrix FiniteRootedTree

variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- The reversed integration clock, not a permutation of stage rows. -/
abbrev reflectedClock (A : Matrix ι ι R) : ι → R := 1 - nodes A

/-- Probe with both ordinary and reflected powers exposed. -/
abbrev reflectedProbe (A : Matrix ι ι R) (b : ι → R) (r k : ℕ) : (ι → R) →ₗ[R] R :=
  row (fun i => b i * (nodes A i)^r * (reflectedClock A i)^k)

@[simp] theorem reflectedProbe_zero_right (A : Matrix ι ι R) (b : ι → R) (r : ℕ)
    (v : ι → R) : reflectedProbe A b r 0 v = probe A b r v := by
  simp only [reflectedProbe, pow_zero, mul_one, probe]

theorem reflectedProbe_succ_right (A : Matrix ι ι R) (b : ι → R) (r k : ℕ)
    (v : ι → R) :
    reflectedProbe A b r (k+1) v =
      reflectedProbe A b r k v - reflectedProbe A b (r+1) k v := by
  simp only [reflectedProbe, row_apply, dotProduct, ← Finset.sum_sub_distrib,
    reflectedClock, Pi.sub_apply, Pi.one_apply, pow_succ]
  apply Finset.sum_congr rfl
  intro i _
  ring

variable {A : Matrix ι ι R} {b : ι → R} {p : ℕ}

/-- The adjacent beta recurrence for the actual normalized stage column.
Only two ordinary normalized probes are needed in the base case. -/
theorem reflectedProbe_norm_shift (ho : HasOrder p A b) (t : FiniteRootedTree)
    (r k : ℕ) (hp : (t.order : ℕ)+r+k+1 ≤ p) :
    ((k+1 : ℕ) : R) * reflectedProbe A b (r+1) k (normTree A t) =
      ((((t.order : ℕ)+r : ℕ) : R)) * reflectedProbe A b r (k+1) (normTree A t) := by
  induction k generalizing r with
  | zero =>
    have h0 := probe_normTree ho t r (by omega)
    have h1 := probe_normTree ho t (r+1) (by omega)
    rw [reflectedProbe_succ_right]
    simp only [Nat.zero_add, Nat.cast_one, one_mul, reflectedProbe_zero_right]
    simp only [Nat.cast_add, Nat.cast_one] at h0 h1 ⊢
    linear_combination h1 - h0
  | succ k ih =>
    have h0 := ih r (by omega)
    have h1 := ih (r+1) (by omega)
    have he := reflectedProbe_succ_right A b (r+1) k (normTree A t)
    rw [reflectedProbe_succ_right A b r (k+1)]
    simp only [Nat.cast_add, Nat.cast_one] at h0 h1 ⊢
    linear_combination h0 - h1 + ((k:R)+1)*he

/-- Unary integration and one ordinary clock power give the same paid
probe on normalized columns (before the unary order factor is stripped). -/
theorem reflectedProbe_unary_eq_clock (ho : HasOrder p A b) (t : FiniteRootedTree)
    (r k : ℕ) (hp : (t.order : ℕ)+r+k+1 ≤ p) :
    reflectedProbe A b r k (normTree A (leaf ◂ t)) =
      reflectedProbe A b (r+1) k (normTree A t) := by
  have ht : ((leaf ◂ t).order : ℕ) = 1 + (t.order : ℕ) := by
    simp only [order, PNat.add_coe, PNat.one_coe]
  induction k generalizing r with
  | zero =>
    simp only [reflectedProbe_zero_right]
    have h0 := probe_normTree ho t (r+1) (by omega)
    have h1 := probe_normTree ho (leaf ◂ t) r (by omega)
    have hdeg : r + ((leaf ◂ t).order : ℕ) = (r+1) + (t.order : ℕ) := by omega
    rw [hdeg] at h1
    exact (IsUnit.of_mul_eq_one _ h0).mul_left_cancel (h1.trans h0.symm)
  | succ k ih =>
    rw [reflectedProbe_succ_right A b r k,
      reflectedProbe_succ_right A b (r+1) k, ih r (by omega), ih (r+1) (by omega)]

/-- The weighted backward input for an integration against the reflected clock. -/
abbrev reflectedStageWeight (A : Matrix ι ι R) (b : ι → R) (k : ℕ) : ι → R :=
  fun i => b i * (reflectedClock A i)^k

/-- The adjoint stage defect D(k+1), as an actual row of stage weights. -/
@[expose] def reflectedStageRow (A : Matrix ι ι R) (b : ι → R) (k : ℕ) : ι → R :=
  ((k+1 : ℕ) : R) • (Aᵀ *ᵥ reflectedStageWeight A b k) - reflectedStageWeight A b (k+1)

theorem reflectedStageRow_pair (A : Matrix ι ι R) (b : ι → R) (k : ℕ) (v : ι → R) :
    row (reflectedStageRow A b k) v =
      ((k+1 : ℕ) : R) * reflectedProbe A b 0 k (mat A v) -
        reflectedProbe A b 0 (k+1) v := by
  simp only [row_apply, reflectedStageRow, sub_dotProduct, smul_dotProduct,
    smul_eq_mul, Matrix.mulVec_transpose, Matrix.dotProduct_mulVec, reflectedProbe,
    pow_zero, mul_one, mat_apply]

theorem reflectedStageRow_normTree (ho : HasOrder p A b) (t : FiniteRootedTree)
    (k : ℕ) (hp : (t.order : ℕ)+k+1 ≤ p) :
    row (reflectedStageRow A b k) (normTree A t) = 0 := by
  have hshift := reflectedProbe_norm_shift ho t 0 k (by omega)
  have hclock := reflectedProbe_unary_eq_clock ho t 0 k (by omega)
  simp only [Nat.zero_add, Nat.add_zero] at hshift hclock
  rw [normTree_unary, map_smul, smul_eq_mul] at hclock
  have hu := ho.natCast_isUnit t.order.pos (by omega : (t.order : ℕ) ≤ p)
  apply hu.mul_left_cancel
  rw [mul_zero, reflectedStageRow_pair, mul_sub, sub_eq_zero]
  calc
    ((t.order : ℕ) : R) * (((k+1 : ℕ) : R) *
        reflectedProbe A b 0 k (mat A (normTree A t))) =
      ((k+1 : ℕ) : R) * (((t.order : ℕ) : R) *
        reflectedProbe A b 0 k (mat A (normTree A t))) := mul_left_comm _ _ _
    _ = ((k+1 : ℕ) : R) * reflectedProbe A b 1 k (normTree A t) :=
      congrArg (fun q : R => ((k+1 : ℕ) : R) * q) hclock
    _ = ((t.order : ℕ) : R) * reflectedProbe A b 0 (k+1) (normTree A t) := hshift

/-- The unscaled reviewed stage profile obeys the exact same paid reverse identity.
The forest multiplier is a proven unit, not merely nonzero. -/
theorem reflectedStageRow_Φ (ho : HasOrder p A b) (t : FiniteRootedTree)
    (k : ℕ) (hp : (t.order : ℕ)+k+1 ≤ p) :
    row (reflectedStageRow A b k) (Φ t A) = 0 := by
  have h := reflectedStageRow_normTree ho t k hp
  rw [normTree, map_smul, smul_eq_mul] at h
  apply (forestFactorial_isUnit ho t (by omega : (t.order : ℕ) ≤ p)).mul_left_cancel
  rwa [mul_zero]

/-- Physical reverse vectors annihilate every rooted-tree column at the
exact complementary vertex grade. No restrictions on individual weights
or diagonal entries are needed for the pairing. -/
theorem reflectedStageRow_treeSpace (ho : HasOrder p A b) (j k : ℕ) (hk : j+k+2≤p) :
    treeSpace A j ≤ LinearMap.ker (row (reflectedStageRow A b k)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t, ht, rfl⟩
  exact reflectedStageRow_Φ ho t k (by omega)

end RKResearch.Certified.Graded
