import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneCompletion

theorem counts {beta gamma : Nat} (hs : 1 + beta + gamma = 6) (hg : 3 ≤ gamma) :
    (beta = 0 ∧ gamma = 5) ∨ (beta = 1 ∧ gamma = 4) ∨ (beta = 2 ∧ gamma = 3) := by
  omega

variable {K : Type*} [Field K]

def eval3 (p0 p1 p2 p3 t : K) : K := p0 + p1*t + p2*t^2 + p3*t^3

/-- Three distinct old reads determine a quadratic without any order on K. -/
theorem quadratic_three_zero
    {p0 p1 p2 a b c : K} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : p0+p1*a+p2*a^2 = 0) (hb : p0+p1*b+p2*b^2 = 0)
    (hc : p0+p1*c+p2*c^2 = 0) : p0 = 0 ∧ p1 = 0 ∧ p2 = 0 := by
  have h₁ : p1+p2*(a+b) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hab)
    linear_combination ha-hb
  have h₂ : p1+p2*(a+c) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hac)
    linear_combination ha-hc
  have h₃ : p2*(b-c) = 0 := by linear_combination h₁-h₂
  have hz₂ : p2 = 0 := (mul_eq_zero.mp h₃).resolve_right (sub_ne_zero.mpr hbc)
  have hz₁ : p1 = 0 := by simpa [hz₂] using h₁
  exact ⟨by simpa [hz₁,hz₂] using ha, hz₁,hz₂⟩

theorem cubic_from_old_roots {p0 p1 p2 p3 a b c : K}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : eval3 p0 p1 p2 p3 a = 0) (hb : eval3 p0 p1 p2 p3 b = 0)
    (hc : eval3 p0 p1 p2 p3 c = 0) (y : K) :
    eval3 p0 p1 p2 p3 y = p3*(y-a)*(y-b)*(y-c) := by
  unfold eval3 at *
  have qa : (p0+p3*a*b*c)+(p1-p3*(a*b+a*c+b*c))*a+(p2+p3*(a+b+c))*a^2 = 0 := by
    linear_combination ha
  have qb : (p0+p3*a*b*c)+(p1-p3*(a*b+a*c+b*c))*b+(p2+p3*(a+b+c))*b^2 = 0 := by
    linear_combination hb
  have qc : (p0+p3*a*b*c)+(p1-p3*(a*b+a*c+b*c))*c+(p2+p3*(a+b+c))*c^2 = 0 := by
    linear_combination hc
  obtain ⟨h₀,h₁,h₂⟩ := quadratic_three_zero hab hac hbc qa qb qc
  linear_combination h₀+y*h₁+y^2*h₂

/-- In the true zero-reciprocal branch the old three live rows already
pin the cubic, and no nonzero lower-degree polynomial can have that head. -/
theorem zero_reciprocal_factor {p0 p1 p2 p3 a b c Ga Gb Gc : K}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hGa : Ga ≠ 0) (hGb : Gb ≠ 0) (hGc : Gc ≠ 0)
    (ha : Ga * eval3 p0 p1 p2 p3 a = 0) (hb : Gb * eval3 p0 p1 p2 p3 b = 0)
    (hc : Gc * eval3 p0 p1 p2 p3 c = 0) (y : K) :
    eval3 p0 p1 p2 p3 y = p3*(y-a)*(y-b)*(y-c) := by
  exact cubic_from_old_roots hab hac hbc ((mul_eq_zero.mp ha).resolve_left hGa)
    ((mul_eq_zero.mp hb).resolve_left hGb) ((mul_eq_zero.mp hc).resolve_left hGc) y

/-- Complementary injectivity of the clean/ghost Z6 samples when the
fourth ordinary reverse row has zero G but live clean barycentric head.
This needs no live reciprocal division at the fourth ordinary row. -/
theorem zero_reciprocal_z6_prefix
    {p0 p1 p2 p3 θ a b c z Ga Gb Gc Gz Ha Hb Hc HV : K}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c)
    (hGa : Ga ≠ 0) (hGb : Gb ≠ 0) (hGc : Gc ≠ 0)
    (hGz : Gz ≠ 0) (hHV : HV ≠ 0)
    (ha : Ga*eval3 p0 p1 p2 p3 a+θ*Ha = 0)
    (hb : Gb*eval3 p0 p1 p2 p3 b+θ*Hb = 0)
    (hc : Gc*eval3 p0 p1 p2 p3 c+θ*Hc = 0)
    (hz : Gz*eval3 p0 p1 p2 p3 z = 0) (hV : θ*HV = 0) :
    θ = 0 ∧ p0 = 0 ∧ p1 = 0 ∧ p2 = 0 ∧ p3 = 0 := by
  have hθ : θ = 0 := (mul_eq_zero.mp hV).resolve_right hHV
  have ha' : Ga*eval3 p0 p1 p2 p3 a = 0 := by simpa [hθ] using ha
  have hb' : Gb*eval3 p0 p1 p2 p3 b = 0 := by simpa [hθ] using hb
  have hc' : Gc*eval3 p0 p1 p2 p3 c = 0 := by simpa [hθ] using hc
  have hz' : eval3 p0 p1 p2 p3 z = 0 := (mul_eq_zero.mp hz).resolve_left hGz
  rw [zero_reciprocal_factor hab hac hbc hGa hGb hGc ha' hb' hc' z] at hz'
  have h₃ : p3 = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp hz').resolve_right
      (sub_ne_zero.mpr hzc))).resolve_right (sub_ne_zero.mpr hzb))).resolve_right
      (sub_ne_zero.mpr hza)
  obtain ⟨h₀,h₁,h₂⟩ := quadratic_three_zero hab hac hbc
    (by simpa [eval3,h₃] using (mul_eq_zero.mp ha').resolve_left hGa)
    (by simpa [eval3,h₃] using (mul_eq_zero.mp hb').resolve_left hGb)
    (by simpa [eval3,h₃] using (mul_eq_zero.mp hc').resolve_left hGc)
  exact ⟨hθ,h₀,h₁,h₂,h₃⟩

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneCompletion

open RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneCompletion
#print axioms counts
#print axioms zero_reciprocal_factor
#print axioms zero_reciprocal_z6_prefix
