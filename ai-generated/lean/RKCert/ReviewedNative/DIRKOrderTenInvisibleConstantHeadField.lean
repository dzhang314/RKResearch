module

public import RKCert.ReviewedNative.DIRKOrderTenInvisibleDistinctSlackField

@[expose] public section

/-! # Constant invisible DIRK ten: one dead dirty read, four live head reads -/
namespace RKResearch.Certified.Graded.InvisibleConstantHeadField

open Lean.Grind
section
variable {K : Type} [Field K]

private theorem cancelScalar (a x : K) (ha : a ≠ 0) (h : a*x=0) : x=0 := by
  have ht := congrArg (fun z => a⁻¹*z) h
  rw [←Semiring.mul_assoc, Field.inv_mul_cancel ha, Semiring.one_mul, Semiring.mul_zero] at ht
  exact ht

/-- A paid row annihilating g can be dead on the unique physical
invisible cubic stage. The geometric proof places this stage early. -/
theorem lone_cubic_read_zero (γ d : K) (hγ : γ≠0) (hg : γ*d=0) : d=0 :=
  cancelScalar γ d hγ hg

/-- With two equal invisible cubic values the two physical reads
are tied before the nonconstant h profile is used. -/
theorem constant_cubic_pair_balance (γ a b : K) (hγ : γ≠0)
    (hg : γ*a+γ*b=0) : a+b=0 := by
  have h : γ*(a+b)=0 := by grind
  exact cancelScalar γ _ hγ h

private theorem zero_three_sites (a b c x y z : K)
    (hab : a-b≠0) (hac : a-c≠0) (hbc : b-c≠0)
    (h₀ : x+y+z=0)
    (h₁ : a*x+b*y+c*z=0)
    (h₂ : a^2*x+b^2*y+c^2*z=0) :
    x=0 ∧ y=0 ∧ z=0 := by
  have v : (a-b)*((a-c)*x)=0 := by grind
  have hx := cancelScalar (a-c) x hac (cancelScalar (a-b) _ hab v)
  have u : (b-c)*y=0 := by grind
  have hy := cancelScalar (b-c) y hbc u
  exact ⟨hx,hy,by grind⟩

/-- A nonzero row on four distinct clock labels annihilating degrees
zero, one, and two is live on every label. -/
theorem four_head_reads_live (a b c d x y z w : K)
    (hab : a-b≠0) (hac : a-c≠0) (had : a-d≠0)
    (hbc : b-c≠0) (hbd : b-d≠0) (hcd : c-d≠0)
    (h₀ : x+y+z+w=0)
    (h₁ : a*x+b*y+c*z+d*w=0)
    (h₂ : a^2*x+b^2*y+c^2*z+d^2*w=0)
    (hne : ¬(x=0 ∧ y=0 ∧ z=0 ∧ w=0)) :
    x≠0 ∧ y≠0 ∧ z≠0 ∧ w≠0 := by
  refine ⟨?_,?_,?_,?_⟩
  · intro hx
    obtain ⟨hy,hz,hw⟩ := zero_three_sites b c d y z w hbc hbd hcd (by grind) (by grind) (by grind)
    exact hne ⟨hx,hy,hz,hw⟩
  · intro hy
    obtain ⟨hx,hz,hw⟩ := zero_three_sites a c d x z w hac had hcd (by grind) (by grind) (by grind)
    exact hne ⟨hx,hy,hz,hw⟩
  · intro hz
    obtain ⟨hx,hy,hw⟩ := zero_three_sites a b d x y w hab had hbd (by grind) (by grind) (by grind)
    exact hne ⟨hx,hy,hz,hw⟩
  · intro hw
    obtain ⟨hx,hy,hz⟩ := zero_three_sites a b c x y z hab hac hbc (by grind) (by grind) (by grind)
    exact hne ⟨hx,hy,hz,hw⟩

end
end RKResearch.Certified.Graded.InvisibleConstantHeadField
