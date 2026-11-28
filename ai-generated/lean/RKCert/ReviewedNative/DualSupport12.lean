module

public import RKCert.ReviewedNative.SufficientGradedFlags
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! For order twelve, low forward defects on zero-weight coordinates and low
reverse defects off those coordinates suffice, with one grade-six bridge.
The scalar cross-moments follow algebraically from the ordinary moments.
There is no positivity, linear dimension or tree enumeration premise. -/

namespace RKResearch.Certified.Graded.DualSupport12

open scoped Matrix

variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- Vectors supported on the indicated ghost rows. -/
def supported (ghost : ι → Prop) (v : ι → R) : Prop :=
  ∀ i, ¬ ghost i → v i = 0

/-- The complementary zero condition for true reverse probes. -/
def zeroAt (ghost : ι → Prop) (z : ι → R) : Prop :=
  ∀ i, ghost i → z i = 0

def reflected (A : Matrix ι ι R) : ι → R := 1 - nodes A

def moment (A : Matrix ι ι R) (b : ι → R) (j : Nat) : ι → R :=
  b * (reflected A)^j

@[simp] theorem moment_zero (A : Matrix ι ι R) (b : ι → R) :
    moment A b 0 = b := by simp [moment]

def forward (A : Matrix ι ι R) (j : Nat) : ι → R :=
  ((j+1 : Nat) : R) • mat A ((nodes A)^j) - (nodes A)^(j+1)

def reverse (A : Matrix ι ι R) (b : ι → R) (j : Nat) : ι → R :=
  ((j+1 : Nat) : R) • mat A.transpose (moment A b j) - moment A b (j+1)

private theorem left_sub (a b v : ι → R) :
    row (a-b) v = row a v - row b v := by
  simp

private theorem left_smul (r : R) (a v : ι → R) :
    row (r • a) v = r * row a v := by
  simp

private theorem dualA (A : Matrix ι ι R) (z v : ι → R) :
    row z (mat A v) = row (mat A.transpose z) v := by
  rw [row_apply, row_apply, mat_apply, mat_apply]
  rw [← Matrix.dotProduct_transpose_mulVec A v z, dotProduct_comm]

private theorem dualClock (x z v : ι → R) :
    row z (x*v) = row (x*z) v := by
  simp only [row_apply, dotProduct, Pi.mul_apply]
  apply Finset.sum_congr rfl
  intro _ _
  ac_rfl

private theorem dualPhysical (A : Matrix ι ι R) (z v : ι → R) :
    row z (nodes A * v) = row z v - row (reflected A * z) v := by
  rw [dualClock, ← left_sub]
  congr 1
  rw [reflected, sub_mul, one_mul, sub_sub_cancel]

private theorem reverse_test (A : Matrix ι ι R) (b v : ι → R) (j : Nat) :
    row (reverse A b j) v =
      ((j+1 : Nat) : R) * row (moment A b j) (mat A v) - row (moment A b (j+1)) v := by
  rw [reverse, left_sub, left_smul, ← dualA]

private theorem forward_test (A : Matrix ι ι R) (z : ι → R) (j : Nat) :
    row z (forward A j) =
      ((j+1 : Nat) : R) * row (mat A.transpose z) ((nodes A)^j) -
        row z ((nodes A)^(j+1)) := by
  rw [forward, map_sub, map_smul, smul_eq_mul, dualA]

private theorem disjoint {ghost : ι → Prop} {z v : ι → R}
    (hz : zeroAt ghost z) (hv : supported ghost v) : row z v = 0 := by
  classical
  rw [row_apply, dotProduct]
  apply Finset.sum_eq_zero
  intro i _
  by_cases h : ghost i
  · simp [hz i h]
  · simp [hv i h]

omit [Fintype ι] in
private theorem mul_supported {ghost : ι → Prop} {v : ι → R}
    (h : supported ghost v) (w : ι → R) : supported ghost (w*v) := by
  intro i hi
  simp [Pi.mul_apply, h i hi]

private theorem ymoment (A : Matrix ι ι R) (b : ι → R) (j : Nat) :
    reflected A * moment A b j = moment A b (j+1) := by
  rw [moment, moment, pow_succ]
  ac_rfl

private theorem scalar_recur (A : Matrix ι ι R) (b : ι → R) (j k : Nat) :
    row (moment A b (j+1)) ((nodes A)^k) =
      row (moment A b j) ((nodes A)^k) -
      row (moment A b j) ((nodes A)^(k+1)) := by
  rw [← ymoment, ← dualClock, reflected, sub_mul, one_mul, map_sub, pow_succ']

/-- Integration by parts for monomials on the clocks X and 1-X.
The proof works by a moment recurrence and uses neither division nor an
ordered scalar field. -/
theorem mixed_scalar (A : Matrix ι ι R) (b : ι → R)
    (scalar : ∀ j < 12, ((j+1 : Nat) : R) * row b ((nodes A)^j) = 1)
    (j k : Nat) (h : j+k+1 < 12) :
    ((k+1 : Nat) : R) * row (moment A b (j+1)) ((nodes A)^k) =
      ((j+1 : Nat) : R) * row (moment A b j) ((nodes A)^(k+1)) := by
  induction j generalizing k with
  | zero =>
    have h0 := scalar k (by omega)
    have h1 := scalar (k+1) (by omega)
    rw [scalar_recur, moment_zero]
    push_cast at h0 h1 ⊢
    linear_combination h0 - h1
  | succ j ih =>
    have h0 := ih k (by omega)
    have h1 := ih (k+1) (by omega)
    have h2 := scalar_recur A b j (k+1)
    rw [scalar_recur A b (j+1) k]
    push_cast at h0 h1 ⊢
    linear_combination h0 - h1 - ((j : R)+1) * h2

/-- An annihilator defined using literal vector probes, without choosing any
basis of the reverse band or the scalar polynomial space. -/
def high (A : Matrix ι ι R) (b : ι → R)
    (B : Nat → Submodule R (ι → R)) (k : Nat) : Submodule R (ι → R) where
  carrier := { v | (∀ z ∈ B k, row z v = 0) ∧
                   (∀ j ≤ k, row (moment A b j) v = 0) }
  zero_mem' := ⟨by simp, by simp⟩
  add_mem' := by
    intro v w hv hw
    exact ⟨fun z hz => by rw [map_add, hv.1 z hz, hw.1 z hz, zero_add],
      fun j hj => by rw [map_add, hv.2 j hj, hw.2 j hj, zero_add]⟩
  smul_mem' := by
    intro r v hv
    exact ⟨fun z hz => by simp [hv.1 z hz], fun j hj => by simp [hv.2 j hj]⟩

@[simp] theorem mem_high {A : Matrix ι ι R} {b : ι → R}
    {B : Nat → Submodule R (ι → R)} {k : Nat} {v : ι → R} :
    v ∈ high A b B k ↔
      (∀ z ∈ B k, row z v = 0) ∧ (∀ j ≤ k, row (moment A b j) v = 0) := Iff.rfl

structure LowChecks (A : Matrix ι ι R) (b : ι → R) where
  ghost : ι → Prop
  fw : Nat → Submodule R (ι → R)
  bw : Nat → Submodule R (ι → R)
  weight_zero : zeroAt ghost b
  fw_zero : ∀ j ≤ 2, fw j = ⊥
  fw_support : ∀ j ≤ 5, ∀ v ∈ fw j, supported ghost v
  bw_support : ∀ j ≤ 5, ∀ z ∈ bw j, zeroAt ghost z
  bw_mono : ∀ j < 5, bw j ≤ bw (j+1)
  fw_A : ∀ j < 5, ∀ v ∈ fw j, mat A v ∈ fw (j+1)
  fw_C : ∀ j < 5, ∀ v ∈ fw j, nodes A * v ∈ fw (j+1)
  fw_primitive : ∀ j < 5, forward A j ∈ fw (j+1)
  bw_A : ∀ j < 5, ∀ z ∈ bw j, mat A.transpose z ∈ bw (j+1)
  bw_Y : ∀ j < 5, ∀ z ∈ bw j, reflected A * z ∈ bw (j+1)
  bw_primitive : ∀ j < 5, reverse A b j ∈ bw (j+1)
  bw_scalar_zero : ∀ j ≤ 5, ∀ k, j+k < 12 → ∀ z ∈ bw j, row z ((nodes A)^k) = 0
  bridge_A : ∀ v ∈ fw 5, mat A v ∈ high A b bw 5
  bridge_primitive : forward A 5 ∈ high A b bw 5
  scalar : ∀ j < 12, ((j+1 : Nat) : R) * row b ((nodes A)^j) = 1
  units : ∀ j < 5, IsUnit (((j+1 : Nat) : R))

namespace LowChecks

variable {A : Matrix ι ι R} {b : ι → R} (C : LowChecks A b)

/-- The reverse-annihilator completion of the low forward flag. -/
def band (d : Nat) : Submodule R (ι → R) :=
  if d ≤ 5 then C.fw d else high A b C.bw (11-d)

private theorem ghost_mem_high {k : Nat} (hk : k ≤ 5) {v : ι → R}
    (hv : supported C.ghost v) : v ∈ high A b C.bw k := by
  apply mem_high.mpr
  refine ⟨fun z hz => disjoint (C.bw_support k hk z hz) hv, fun j _ => disjoint ?_ hv⟩
  intro i hi
  simp [moment, Pi.mul_apply, C.weight_zero i hi]

private theorem bw_mono_all {a k : Nat} (ha : a ≤ k) (hk : k ≤ 5) :
    C.bw a ≤ C.bw k := by
  induction k with
  | zero => have e : a = 0 := by omega
            subst a
            exact le_rfl
  | succ k ih =>
    by_cases e : a = k+1
    · rw [e]
    · exact (ih (by omega) (by omega)).trans (C.bw_mono k (by omega))

private theorem high_A {k : Nat} (hk : k < 5) {v : ι → R}
    (hv : v ∈ high A b C.bw (k+1)) : mat A v ∈ high A b C.bw k := by
  rcases mem_high.mp hv with ⟨hvB, hvP⟩
  apply mem_high.mpr
  refine ⟨fun z hz => ?_, fun j hj => ?_⟩
  · rw [dualA]
    exact hvB _ (C.bw_A k hk z hz)
  · have e := hvB _ (C.bw_mono_all (show j+1 ≤ k+1 by omega) (by omega) (C.bw_primitive j (by omega)))
    rw [reverse_test, hvP (j+1) (by omega), sub_zero] at e
    exact (C.units j (by omega)).mul_left_cancel (e.trans (mul_zero _).symm)

private theorem high_C {k : Nat} (hk : k < 5) {v : ι → R}
    (hv : v ∈ high A b C.bw (k+1)) : nodes A * v ∈ high A b C.bw k := by
  rcases mem_high.mp hv with ⟨hvB, hvP⟩
  apply mem_high.mpr
  refine ⟨fun z hz => ?_, fun j hj => ?_⟩
  · rw [dualPhysical, hvB _ (C.bw_mono k hk hz), hvB _ (C.bw_Y k hk z hz), sub_zero]
  · rw [dualPhysical, ymoment, hvP j (by omega), hvP (j+1) (by omega), sub_zero]

private theorem high_primitive {j : Nat} (hj : 6 ≤ j) (hp : j+1 < 12) :
    forward A j ∈ high A b C.bw (10-j) := by
  have hk : 10-j < 5 := by omega
  apply mem_high.mpr
  refine ⟨fun z hz => ?_, fun k hk' => ?_⟩
  · rw [forward_test,
        C.bw_scalar_zero (10-j+1) (by omega) j (by omega) _ (C.bw_A (10-j) hk z hz),
        C.bw_scalar_zero (10-j) (by omega) (j+1) (by omega) _ hz, mul_zero, sub_zero]
  · have h := C.bw_scalar_zero (k+1) (by omega) j (by omega) _ (C.bw_primitive k (by omega))
    rw [reverse_test, sub_eq_zero] at h
    have m := mixed_scalar A b C.scalar k j (by omega)
    rw [forward, map_sub, map_smul, smul_eq_mul, sub_eq_zero]
    have hm : ((k+1 : Nat) : R) *
            (((j+1 : Nat) : R) * row (moment A b k) (mat A ((nodes A)^j))) =
            ((k+1 : Nat) : R) * row (moment A b k) ((nodes A)^(j+1)) := by
      rw [mul_left_comm, h, m]
    exact (C.units k (by omega)).mul_left_cancel hm

def flags : SufficientFlags 12 A b where
  band := C.band
  stepA := by
    intro d hd v hv
    by_cases hlo : d+1 ≤ 5
    · simpa [band, hlo] using C.fw_A d (by omega) v (by simpa [band, show d ≤ 5 by omega] using hv)
    by_cases heq : d = 5
    · subst d
      simpa [band] using C.bridge_A v (by simpa [band] using hv)
    · have e : 11-d = 11-(d+1)+1 := by omega
      apply (show mat A v ∈ high A b C.bw (11-(d+1)) → _ by simp [band, hlo])
      apply C.high_A (by omega)
      rw [← e]
      simpa only [band, ite_eq_right (show ¬ d ≤ 5 by omega)] using hv
  stepC := by
    intro d hd v hv
    by_cases hlo : d+1 ≤ 5
    · simpa [band, hlo] using C.fw_C d (by omega) v (by simpa [band, show d ≤ 5 by omega] using hv)
    by_cases heq : d = 5
    · subst d
      have hs := C.fw_support 5 (by omega) v (by simpa [band] using hv)
      simpa [band] using C.ghost_mem_high (k:=5) (by omega) (mul_supported hs (nodes A))
    · have e : 11-d = 11-(d+1)+1 := by omega
      apply (show nodes A * v ∈ high A b C.bw (11-(d+1)) → _ by simp [band, hlo])
      apply C.high_C (by omega)
      rw [← e]
      simpa only [band, ite_eq_right (show ¬ d ≤ 5 by omega)] using hv
  mulBand := by
    intro d e hde v w hv hw
    by_cases hd : d ≤ 2
    · have h : v = 0 := by simpa [band, show d ≤ 5 by omega, C.fw_zero d hd] using hv
      simp [h]
    by_cases he : e ≤ 2
    · have h : w = 0 := by simpa [band, show e ≤ 5 by omega, C.fw_zero e he] using hw
      simp [h]
    have hsum : ¬ d+e ≤ 5 := by omega
    apply (show v*w ∈ high A b C.bw (11-(d+e)) → _ by simp [band, hsum])
    apply C.ghost_mem_high (by omega)
    by_cases hl : d ≤ 5
    · rw [mul_comm]
      exact mul_supported (C.fw_support d hl v (by simpa [band, hl] using hv)) w
    · have hl' : e ≤ 5 := by omega
      exact mul_supported (C.fw_support e hl' w (by simpa [band, hl'] using hw)) v
  primitive := by
    intro d hd
    change forward A d ∈ C.band (d+1)
    by_cases hl : d+1 ≤ 5
    · simpa [band, hl] using C.fw_primitive d (by omega)
    by_cases he : d = 5
    · subst d
      simpa [band] using C.bridge_primitive
    have eq : 11-(d+1) = 10-d := by omega
    simpa [band, hl, eq] using C.high_primitive (j:=d) (by omega) hd
  silent := by
    intro d hd v hv
    by_cases hl : d ≤ 5
    · exact disjoint C.weight_zero (C.fw_support d hl v (by simpa [band, hl] using hv))
    · have hh : v ∈ high A b C.bw (11-d) := by simpa [band, hl] using hv
      simpa using (mem_high.mp hh).2 0 (by omega)
  scalar := C.scalar

theorem hasOrder (checks : LowChecks A b) : RKResearch.HasOrder 12 A b :=
  SufficientFlags.hasOrder (flags checks)

end LowChecks

end RKResearch.Certified.Graded.DualSupport12

#print axioms RKResearch.Certified.Graded.DualSupport12.mixed_scalar
#print axioms RKResearch.Certified.Graded.DualSupport12.LowChecks.hasOrder
