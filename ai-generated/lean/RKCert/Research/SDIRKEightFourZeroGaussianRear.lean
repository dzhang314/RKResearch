import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Scalar receipts for the literal reverse ghost and Gaussian rear charts.
Flag saturation and resultant projection are supplied separately. -/
namespace RKResearch.Certified.SDIRKEightFourZeroGaussianRear

def K {R : Type*} [CommRing R] (v : R) : R := 1 + 2*v - v^2
def H {R : Type*} [CommRing R] (v : R) : R := -2 + v + 4*v^2 - v^3

theorem silent_eighth_cubic {F : Type*} [Field F] {v : F}
    (hv : v ≠ 0) (hr : 4*v^2 = K v * (K v - 1)) : H v = 0 := by
  have h : v * H v = 0 := by
    calc
      v * H v = 4*v^2 - K v * (K v - 1) := by unfold H K; ring
      _ = 0 := sub_eq_zero.mpr hr
  exact (mul_eq_zero.mp h).resolve_left hv

theorem silent_eighth_not_zero_second {F : Type*} [Field F] {v : F}
    (hv : v ≠ 0) (h₄ : (4 : F) ≠ 0)
    (hr : 4*v^2 = K v * (K v - 1)) : K v ≠ 0 := by
  intro hk
  have hl : 4 * v^2 = 0 := by simpa [hk] using hr
  exact (mul_ne_zero h₄ (pow_ne_zero 2 hv)) hl

theorem live_star_clock_even_when_zero_second {F : Type*} [Field F] {v w : F}
    (hw : w ≠ 0) (hneq : w ≠ v)
    (he : w*(1+2*w-w^2)=K v*w) : w=2-v := by
  have hh : w * ((w-v)*(2-w-v)) = 0 := by
    calc
      w * ((w-v)*(2-w-v)) = w*(1+2*w-w^2)-K v*w := by unfold K; ring
      _ = 0 := sub_eq_zero.mpr he
  have hh' := (mul_eq_zero.mp hh).resolve_left hw
  have ht : 2-w-v=0 := (mul_eq_zero.mp hh').resolve_left (sub_ne_zero.mpr hneq)
  calc
    w = 2-v-(2-w-v) := by ring
    _ = 2-v := by rw [ht, sub_zero]

theorem integer_norm_products :
    (22934064120100000000 : Nat) = 2^8 * 5^8 * 7^5 * 17 * 103 * 7793 ∧
    (2920662406109593600000000 : Nat) = 2^30 * 5^8 * 7^4 * 13^2 * 131^2 := by
  decide +kernel

end RKResearch.Certified.SDIRKEightFourZeroGaussianRear
