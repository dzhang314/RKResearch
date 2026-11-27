import Lean

/-! Scalar leaves for the nonconstant-amplitude localized ERK10 chart. -/
namespace RKResearch.ERK10NonconstantAmplitudeGate
open Lean.Grind
variable {K : Type} [Field K]

private theorem nzMul {a b : K} (na : a ≠ 0) (nb : b ≠ 0) : a*b ≠ 0 :=
  fun z => nb ((Field.of_mul_eq_zero z).resolve_left na)

private theorem cubeNe {u : K} (nu : u ≠ 0) : u^3 ≠ 0 := by
  have hh : u^3=(u*u)*u := by grind
  rw [hh]
  exact nzMul (nzMul nu nu) nu

theorem sixthMomentExpansion (d a : K) :
    (d*(d-a))^3=d^6-3*a*d^5+3*a^2*d^4-a^3*d^3 := by grind

theorem repeatImpliesDoubleContact (x y u : K)
    (hd : x=2*y) (h : 3*u^2-4*(x+y)*u+6*x*y=0)
    (n3 : (3:K) ≠ 0) : u=x := by
  have hp : (3:K)*((u-x)*(u-x))=0 := by grind
  rcases Field.of_mul_eq_zero ((Field.of_mul_eq_zero hp).resolve_left n3) with hz | hz
  · grind
  · grind

theorem beforeContact (p u b c : K)
    (nu : u ≠ 0)
    (h₂ : 3*(b+c*p^2)=u^3) (h₃ : 4*(b+c*p^3)=u^4)
    (h : b+c*p^2*(3-2*p)=0)
    (hp : 3*u^2-4*(1+p)*u+6*p=0)
    (n2 : (2:K) ≠ 0) : u=p := by
  have he : u^3*(2-u) =
      2*(b+c*p^2*(3-2*p))+2*(u^3-3*(b+c*p^2))-(u^4-4*(b+c*p^3)) := by
    clear nu h₂ h₃ h hp n2
    grind
  rw [h,h₂,h₃] at he
  have hn : u^3*(2-u)=0 := by
    clear nu h₂ h₃ h hp n2
    grind
  have hq := (Field.of_mul_eq_zero hn).resolve_left (cubeNe nu)
  clear h₂ h₃ h he hn
  have hh : (2:K)*(2-p)=0 := by grind
  have hz := (Field.of_mul_eq_zero hh).resolve_left n2
  grind

theorem interleavedCalibration (p x n a b : K)
    (quadratic : 2*a+2*p*b=2*x+1)
    (cubic : 2*p*a+3*p^2*b-1=2*x)
    (shape : -n*a=x*(2*x+1))
    (different : 2*x+1 ≠ 0) :
    n*(2-3*p)=2*p*x := by
  have h₁ : 2*p*a=(3*p-2)*(2*x+1) := by grind
  have h₂ : (2*x+1)*(n*(2-3*p)-2*p*x)=0 := by grind
  have hh := (Field.of_mul_eq_zero h₂).resolve_left different
  grind

theorem interleavedContact (p u b c : K)
    (nu : u ≠ 0) (np : p ≠ 0) (n2 : (2:K) ≠ 0) (n3 : (3:K) ≠ 0)
    (h₂ : 3*(b+c*p^2)=u^3) (h₃ : 4*(b+c*p^3)=u^4)
    (h : (2-3*p)*b=p^3*c)
    (hp : 3*u^2-4*(1+p)*u+6*p=0) : u=1 := by
  have hid : 6*u^3*(u-2*p)=
      12*((2-3*p)*b-p^3*c)+6*(u^4-4*(b+c*p^3))-12*p*(u^3-3*(b+c*p^2)) := by
    clear nu np n2 n3 h₂ h₃ h hp
    grind
  rw [h,h₂,h₃] at hid
  have hn : 6*u^3*(u-2*p)=0 := by
    clear nu np n2 n3 h₂ h₃ h hp
    grind
  have n6 : (6:K) ≠ 0 := by
    have h6 : (2:K)*3=6 := by grind
    rw [← h6]
    exact nzMul n2 n3
  have hq := (Field.of_mul_eq_zero hn).resolve_left (nzMul n6 (cubeNe nu))
  clear h₂ h₃ h hid hn n6
  have he : 2*p*(2*p-1)=0 := by grind
  have hh := (Field.of_mul_eq_zero he).resolve_left (nzMul n2 np)
  grind

end RKResearch.ERK10NonconstantAmplitudeGate
#print axioms RKResearch.ERK10NonconstantAmplitudeGate.sixthMomentExpansion
#print axioms RKResearch.ERK10NonconstantAmplitudeGate.repeatImpliesDoubleContact
#print axioms RKResearch.ERK10NonconstantAmplitudeGate.beforeContact
#print axioms RKResearch.ERK10NonconstantAmplitudeGate.interleavedCalibration
#print axioms RKResearch.ERK10NonconstantAmplitudeGate.interleavedContact
