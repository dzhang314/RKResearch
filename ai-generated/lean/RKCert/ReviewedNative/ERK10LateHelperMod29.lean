module

public import RKCert.ReviewedNative.ERK10LateHelperGate
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! # Projective residue obstruction for an ERK10 late-helper family

This checks the two homogeneous factors of the pressure reduction modulo
29. The extraction of this reduced polynomial from the rational stage
profile is given in the accompanying exact arithmetic replay. -/

namespace RKResearch.Certified.ERK10LateHelperMod29

open scoped BigOperators

abbrev K := ZMod 29

local instance : Fact (Nat.Prime 29) := ⟨by decide +kernel⟩

def homog (n : ℕ) (v : Fin (n+1) → K) (a b : K) : K :=
  ∑ i, v i * a ^ i.val * b ^ (n-i.val)

def endCoeff : Fin 10 → K := ![4,7,20,1,24,10,20,12,20,20]
def donorCoeff : Fin 3 → K := ![21,23,1]

theorem homog_scale (n : ℕ) (v : Fin (n+1) → K) (a b t : K) :
    homog n v (a*t) (b*t) = homog n v a b * t^n := by
  unfold homog
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_pow]
  calc
    v i * (a ^ i.val * t ^ i.val) * (b ^ (n-i.val) * t ^ (n-i.val)) =
        (v i * a ^ i.val * b ^ (n-i.val)) * (t ^ i.val * t ^ (n-i.val)) := by ring
    _ = _ := by
      have h : i.val + (n-i.val) = n := by have hi := i.isLt; omega
      rw [←pow_add,h]

theorem nonzero_of_projective_charts (n : ℕ) (v : Fin (n+1) → K)
    (ha : ∀ a : K, homog n v a 1 ≠ 0) (hi : homog n v 1 0 ≠ 0)
    {a b : K} (hab : a ≠ 0 ∨ b ≠ 0) : homog n v a b ≠ 0 := by
  intro h
  by_cases hb : b = 0
  · have hz : a ≠ 0 := hab.resolve_right (not_not_intro hb)
    have q := homog_scale n v a b a⁻¹
    rw [h,zero_mul,mul_inv_cancel₀ hz,hb,zero_mul] at q
    exact hi q
  · have q := homog_scale n v a b b⁻¹
    rw [h,zero_mul,mul_inv_cancel₀ hb] at q
    exact ha (a*b⁻¹) q

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem endpoint_affine : ∀ a : K, homog 9 endCoeff a 1 ≠ 0 := by decide +kernel

theorem endpoint_infinity : homog 9 endCoeff 1 0 ≠ 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem donor_affine : ∀ a : K, homog 2 donorCoeff a 1 ≠ 0 := by decide +kernel

theorem donor_infinity : homog 2 donorCoeff 1 0 ≠ 0 := by decide +kernel

/-- No zero is hidden at infinity in either the endpoint or the donor
coordinate. This allows both horizon and donor to have poles at 29. -/
theorem pressure_nonzero {a b c d : K}
    (he : a ≠ 0 ∨ b ≠ 0) (hd : c ≠ 0 ∨ d ≠ 0) :
    homog 9 endCoeff a b * homog 2 donorCoeff c d ≠ 0 :=
  mul_ne_zero (nonzero_of_projective_charts 9 endCoeff endpoint_affine endpoint_infinity he)
    (nonzero_of_projective_charts 2 donorCoeff donor_affine donor_infinity hd)

end RKResearch.Certified.ERK10LateHelperMod29

#print axioms RKResearch.Certified.ERK10LateHelperMod29.pressure_nonzero
