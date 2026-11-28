import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSlackChronology

variable {K : Type*} [Field K]

/-- Two distinct physical G/b profiles (or one actual silent live G)
cannot share the two paid primitives of a two-nonzero-clock prefix.
The clocks may be negative or numerical contacts. -/
theorem two_clock_same_label_impossible
    {u v b0 b1 G0 G1 l q : K}
    (nu : u≠0) (s : b0*G1-b1*G0≠0)
    (a0 : b0*(u^3*(2*v-u))=G0*l)
    (a1 : b1*(u^3*(2*v-u))=G1*l)
    (j0 : b0*(u^4*(5*v-3*u))=G0*q)
    (j1 : b1*(u^4*(5*v-3*u))=G1*q) : False := by
  have ep : (b0*G1-b1*G0)*(u^3*(2*v-u))=0 := by
    linear_combination G1*a0-G0*a1
  have ej : (b0*G1-b1*G0)*(u^4*(5*v-3*u))=0 := by
    linear_combination G1*j0-G0*j1
  have eu : 2*v-u=0 := (mul_eq_zero.mp
    ((mul_eq_zero.mp ep).resolve_left s)).resolve_left (pow_ne_zero 3 nu)
  have ev : 5*v-3*u=0 := (mul_eq_zero.mp
    ((mul_eq_zero.mp ej).resolve_left s)).resolve_left (pow_ne_zero 4 nu)
  have vz : v=0 := by linear_combination 3*eu-ev
  exact nu (by linear_combination 2*vz-eu)

/-- If two ordinary pair members differ in the given reverse normalized
head, two zero commutator reads separate both coefficients at the label. -/
theorem paid_pair_zero {a b h P theta : K} (hab : a≠b) (hh : h≠0)
    (ha : a*P+theta*h=0) (hb : b*P+theta*h=0) : P=0 ∧ theta=0 := by
  have hp : (a-b)*P=0 := by linear_combination ha-hb
  have zp : P=0 := (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hab)
  have ht : theta*h=0 := by simpa [zp] using ha
  exact ⟨zp,(mul_eq_zero.mp ht).resolve_right hh⟩

section Ring

variable {R : Type*} [CommRing R]

theorem pre_fourth_repeat_factor {J K w lambda q0 q1 : R}
    (r0 : J-lambda*q0=w*(K-q0))
    (r1 : J-lambda*q1=w*(K-q1)) :
    (w-lambda)*(q1-q0)=0 := by
  linear_combination r1-r0

/-- The exact pre-fifth factor, before any prime or nonzero test. -/
theorem pre_fifth_repeat_factor {J K L w a lambda R0 chi H q0 q1 : R}
    (r0 : L+R0*q0+chi*H=(w+a)*(J-lambda*q0)-w*a*(K-q0))
    (r1 : L+R0*q1+chi*H=(w+a)*(J-lambda*q1)-w*a*(K-q1)) :
    ((w+a)*lambda-w*a+R0)*(q1-q0)=0 := by
  linear_combination r1-r0

end Ring
end RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSlackChronology

open RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSlackChronology
#print axioms two_clock_same_label_impossible
#print axioms paid_pair_zero
#print axioms pre_fourth_repeat_factor
#print axioms pre_fifth_repeat_factor
