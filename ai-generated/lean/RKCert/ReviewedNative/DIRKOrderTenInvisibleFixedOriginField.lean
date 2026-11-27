module

public import RKCert.ReviewedNative.DIRKOrderTenInvisibleOffSlackField

@[expose] public section

/-! # Signed h moment gates for fixed-origin invisible DIRK charts -/
namespace RKResearch.Certified.Graded.InvisibleFixedOriginField

open Lean.Grind
section
variable {K : Type} [Field K]

private theorem cancelScalar (a x : K) (ha : a ≠ 0) (h : a*x=0) : x=0 := by
  have ht := congrArg (fun z => a⁻¹*z) h
  rw [←Semiring.mul_assoc, Field.inv_mul_cancel ha, Semiring.one_mul, Semiring.mul_zero] at ht
  exact ht

/-- Two distinct nonzero exterior h values cannot have nonzero
weights if both their first and second signed h moments vanish. -/
theorem distinct_nonzero_heads_zero_weights (h₁ h₂ b₁ b₂ : K)
    (nh₁ : h₁≠0) (nh₂ : h₂≠0) (nh : h₁-h₂≠0)
    (hm₁ : b₁*h₁+b₂*h₂=0) (hm₂ : b₁*h₁^2+b₂*h₂^2=0) :
    b₁=0 ∧ b₂=0 := by
  have hz : (h₁-h₂)*(h₁*b₁)=0 := by grind
  have hb₁ := cancelScalar h₁ b₁ nh₁ (cancelScalar (h₁-h₂) _ nh hz)
  have hy : h₂*b₂=0 := by grind
  exact ⟨hb₁,cancelScalar h₂ b₂ nh₂ hy⟩

/-- An actual repeated nonzero h class has opposite weights and the
singleton third row has h=0 and the prescribed ordinary mass. -/
theorem repeated_head_splits_clean_pair (h r b₁ b₂ b₃ m : K)
    (nh : h≠0) (nm : m≠0)
    (hm₀ : b₁+b₂+b₃=m) (hm₁ : (b₁+b₂)*h+b₃*r=0)
    (hm₂ : (b₁+b₂)*h^2+b₃*r^2=0) :
    r=0 ∧ b₁+b₂=0 ∧ b₃=m := by
  have hh : m*(h*r)=0 := by grind
  have zr := cancelScalar h r nh (cancelScalar m (h*r) nm hh)
  have hb : h*(b₁+b₂)=0 := by grind
  have za := cancelScalar h (b₁+b₂) nh hb
  exact ⟨zr,za,by grind⟩

/-- At a clean-origin duplicate, its A row is identically zero, so
the genuine reflected normalization uses only the late physical row. -/
theorem normalize_zero_origin_pair (κ b G₀ G₁ a : K) (hκ : κ≠0)
    (h₁ : G₁=κ*b) :
    (G₀*0+G₁*a)/κ=b*a := by
  have h : G₀*0+G₁*a=(b*a)*κ := by rw [h₁]; grind
  rw [h,Field.div_eq_mul_inv,Semiring.mul_assoc,Field.mul_inv_cancel hκ,Semiring.mul_one]

end
end RKResearch.Certified.Graded.InvisibleFixedOriginField
