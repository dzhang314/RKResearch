import Lean

/-! Paid scalar gates for the localized constant-amplitude ERK10 branch. -/
namespace RKResearch.ERK10DependentPairGate
open Lean.Grind
variable {K : Type} [Field K]

private theorem nzMul {x y : K} (nx : x ≠ 0) (ny : y ≠ 0) : x*y ≠ 0 :=
  fun h => ny ((Field.of_mul_eq_zero h).resolve_left nx)

theorem opposingPair (bi bj ri rj : K)
    (nbi : bi ≠ 0) (nri : ri ≠ 0)
    (h₁ : bi*ri+bj*rj=0) (h₂ : bi*ri^2+bj*rj^2=0) :
    ri=rj ∧ bi+bj=0 := by
  have z : (bi*ri)*(ri-rj)=0 := by grind
  have h := (Field.of_mul_eq_zero z).resolve_left (nzMul nbi nri)
  have he : ri=rj := by grind
  rw [← he] at h₁
  have zz : (bi+bj)*ri=0 := by grind
  exact ⟨he,(Field.of_mul_eq_zero zz).resolve_right nri⟩

theorem threeCharges (x y z U V W : K)
    (nxy : x-y ≠ 0) (nxz : x-z ≠ 0) (nyz : y-z ≠ 0)
    (ha : U+V+W=0) (hb : x*U+y*V+z*W=0)
    (zero : U=0 ∨ V=0 ∨ W=0) :
    U=0 ∧ V=0 ∧ W=0 := by
  rcases zero with hu | hv | hw
  · have h : (y-z)*V=0 := by grind
    have hv := (Field.of_mul_eq_zero h).resolve_left nyz
    exact ⟨hu,hv,by grind⟩
  · have h : (x-z)*U=0 := by grind
    have hu := (Field.of_mul_eq_zero h).resolve_left nxz
    exact ⟨hu,hv,by grind⟩
  · have h : (x-y)*U=0 := by grind
    have hu := (Field.of_mul_eq_zero h).resolve_left nxy
    exact ⟨hu,by grind,hw⟩

theorem pairDifferences (theta alpha beta a r s x₀ x₁ x₂ x₃ : K)
    (nθα : theta-alpha ≠ 0) (nθβ : theta-beta ≠ 0) (nαβ : alpha-beta ≠ 0)
    (na : a ≠ 0) (nr : r ≠ 0) (ns : s ≠ 0)
    (h₀ : x₀+x₁=0) (h₁ : a*x₁+r*x₂+s*x₃=0)
    (h₂ : theta*(a*x₁)+alpha*(r*x₂)+beta*(s*x₃)=0)
    (zero : x₀=0 ∨ x₁=0 ∨ x₂=0 ∨ x₃=0) :
    x₀=0 ∧ x₁=0 ∧ x₂=0 ∧ x₃=0 := by
  have zm : a*x₁=0 ∨ r*x₂=0 ∨ s*x₃=0 := by
    rcases zero with e | e | e | e
    · left; grind
    · left; grind
    · right; left; grind
    · right; right; grind
  obtain ⟨p,q,t⟩ := threeCharges theta alpha beta (a*x₁) (r*x₂) (s*x₃)
    nθα nθβ nαβ h₁ h₂ zm
  have j := (Field.of_mul_eq_zero p).resolve_left na
  exact ⟨by grind,j,(Field.of_mul_eq_zero q).resolve_left nr,
      (Field.of_mul_eq_zero t).resolve_left ns⟩

end RKResearch.ERK10DependentPairGate
#print axioms RKResearch.ERK10DependentPairGate.opposingPair
#print axioms RKResearch.ERK10DependentPairGate.threeCharges
#print axioms RKResearch.ERK10DependentPairGate.pairDifferences
