module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Native scalar and quadratic norm receipts for the pure supported polynomial -/

namespace RKResearch.Certified.SDIRKEightFourPurePolynomial

theorem opposite_zero_gaps {K : Type*} [Field K] {u : K}
    (h₂ : (2 : K) ≠ 0) (h₄ : (4 : K) ≠ 0) (hu : u ≠ 0)
    (hf : 4*u^3-12*u^2+3*u+2=0) (hr : 4*(-u)^3-12*(-u)^2+3*(-u)+2=0) :
    6*u^2=1 ∧ (22 : K)=0 := by
  have he : (4 : K)*(1-6*u^2)=0 := by linear_combination hf+hr
  have ho : (2*u)*(4*u^2+3)=0 := by linear_combination hf-hr
  have ha : 6*u^2=1 := by linear_combination -(mul_eq_zero.mp he).resolve_left h₄
  have hb := (mul_eq_zero.mp ho).resolve_left (mul_ne_zero h₂ hu)
  exact ⟨ha,by linear_combination 6*hb-4*ha⟩

theorem determinant_quadratic_norm {R : Type*} [CommRing R] {a b x y k q : R}
    (h₁ : x+y = -k) (h₂ : x*y=q) :
    (a+b*x)*(a+b*y)=a^2-k*a*b+q*b^2 := by
  calc
    (a+b*x)*(a+b*y)=a^2+a*b*(x+y)+b^2*(x*y) := by ring
    _ = a^2-k*a*b+q*b^2 := by rw [h₁,h₂]; ring

theorem literal_augmented_norms :
    ((289010734 : ZMod 770514337)^2-319570959*289010734*692783714+
      537196966*692783714^2=170900925) ∧
    ((17164986678066544640509 : ZMod 26254266039604698273071)^2-
      10931918996081537634502*17164986678066544640509*7327693306740711712779+
      43800998913746017963*7327693306740711712779^2=306422335611480264695) := by
  decide +kernel

end RKResearch.Certified.SDIRKEightFourPurePolynomial
