module

public import RKCert.ReviewedNative.DIRKOrderTenInvisibleConstantHeadField

@[expose] public section

/-! # Local field cancellation at the first regular row in stage five -/
namespace RKResearch.Certified.Graded.InvisibleConstantFourHeadField

open Lean.Grind
variable {K : Type} [Field K]

private theorem cancelScalar (a x : K) (ha : a ≠ 0) (h : a*x=0) : x=0 := by
  have ht := congrArg (fun z => a⁻¹*z) h
  rw [←Semiring.mul_assoc, Field.inv_mul_cancel ha, Semiring.one_mul, Semiring.mul_zero] at ht
  exact ht

/-- The literal zero Volterra row and A h=0 at the first regular
stage force the h-affine slope to be −1. All earlier donor
divisions have been replaced by explicit scalar hypotheses. -/
theorem first_five_h_slope
    (a b r da db wA wB ba hA hB m n : K)
    (hnWB : wB≠0) (hnHB : hB≠0) (hba : b-a≠0)
    (h₀ : wA*hA+wB*hB=0)
    (h₁ : wB*ba=(r-a-da)*wA)
    (h₂ : db=r-b)
    (h₃ : m+n*a=da)
    (h₄ : (m+n*b-db)*hB=ba*hA) :
    n = -1 := by
  have v : wB * (hB * ((m+n*b-db)+(r-a-da))) = 0 := by
    calc
      _ = wB*((m+n*b-db)*hB)+(r-a-da)*(wB*hB) := by grind
      _ = (wB*ba)*hA+(r-a-da)*(wB*hB) := by rw [h₄]; grind
      _ = (r-a-da)*(wA*hA+wB*hB) := by rw [h₁]; grind
      _ = 0 := by rw [h₀,Semiring.mul_zero]
  have z := cancelScalar hB _ hnHB (cancelScalar wB _ hnWB v)
  have f : (b-a)*(n+1)=0 := by
    clear h₀ h₁ h₄ v
    grind
  have g := cancelScalar (b-a) _ hba f
  clear h₀ h₁ h₂ h₃ h₄ v z f
  grind

end RKResearch.Certified.Graded.InvisibleConstantFourHeadField
