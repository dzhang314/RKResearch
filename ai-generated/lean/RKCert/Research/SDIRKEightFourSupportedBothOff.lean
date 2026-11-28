module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Native literal arithmetic receipts for the four-supported-zero branch -/

namespace RKResearch.Certified.SDIRKEightFourSupportedBothOff

theorem zero_gap_bezout {R : Type*} [CommRing R] (u : R) :
    (23*u^3-70*u^2+18*u+48)*(4*u^3-12*u^2+3*u+2)+
      (-92*u^2+188*u-45)*((1+2*u-u^2)^2-1)=96 := by ring

theorem endpoint_ratio_one_factor {R : Type*} [CommRing R] (u : R) :
    (2*u-2)*(-2+u+4*u^2-u^3)-2*u*(3*u-2) =
      -2*(u-2)*(u^3-3*u^2+1) := by ring

theorem odd_block_subtract {R : Type*} [CommRing R] {p q γ a b J₁ J₂ : R}
    (hp : p=q) (h₁ : p*a+γ*b=J₁) (h₂ : q*a+3*γ*b=J₂) :
    J₂-J₁=2*γ*b := by linear_combination h₁-h₂-a*hp

theorem square_pin {R : Type*} [CommRing R] {y B C : R}
    (h : y*B+C=0) : y^2*B^2-C^2=0 := by
  linear_combination (y*B-C)*h

theorem quarter_conflict {R : Type*} [CommRing R] {γ x : R}
    (h₃ : (3 : R) ≠ 0) (hq : 4*γ=1)
    (hp : x^2-4*γ*x+2*γ^2=0) (hG : 28*(2*x-1)^2=17) : False := by
  have hh : 2*(2*x-1)^2=1 := by
    linear_combination 8*hp+(8*x-4*γ-1)*hq
  apply h₃
  linear_combination 14*hh-hG

theorem finite_guards :
    (18 : ZMod 277)*2^2-93^2=10 ∧
    (731209713 : ZMod 2014914997)*1370748104^2-1742426972^2=999087437 := by
  decide +kernel

end RKResearch.Certified.SDIRKEightFourSupportedBothOff
