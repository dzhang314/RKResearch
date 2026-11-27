module

public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8SingletonSlopeReceipts

section Algebra

variable {K : Type*} [CommRing K]

def kap (u : K) : K := 1+2*u-u^2
def tapCubic (u : K) : K := -2+u+4*u^2-u^3

structure Jet (K : Type*) where
  p : K
  d₁ : K
  d₂ : K
  d₃ : K
  deriving DecidableEq

def Jet.value (j : Jet K) (u : K) : K := j.p+j.d₁*u+j.d₂*u^2+j.d₃*u^3

def Jet.second (j : Jet K) (u : K) : K :=
  j.d₁-2*j.p+(j.d₂+j.p)*u+j.d₃*u^2

def Jet.starGuard (j : Jet K) : K := j.d₂+2*j.d₃+j.p

/-- Cubic coefficients in descending degree. -/
def Jet.cubicCoeffs (j : Jet K) : K × K × K × K :=
  (2*j.starGuard, 3*j.d₁-4*j.d₂+7*j.d₃-10*j.p,
    -8*j.d₁+5*j.d₂-6*j.d₃+15*j.p, 4*j.d₁-2*j.d₂-6*j.p)

def Jet.cubic (j : Jet K) (u : K) : K :=
  let (A,B,C,D) := j.cubicCoeffs
  A*u^3+B*u^2+C*u+D

/-- Factorization of the actual third-row arithmetic-branch gate after
substitution of the normalized second-row slope. -/
theorem arithmetic_factor (j : Jet K) (u : K) :
    tapCubic u*kap u*j.value (2*u) -
      (tapCubic u*kap (2*u)+4*u^2*(3*u-2))*(j.p*kap u+2*u*j.second u)
    = 2*u^2*kap u*j.cubic u := by
  simp only [tapCubic,kap,Jet.value,Jet.second,Jet.cubic,Jet.cubicCoeffs,Jet.starGuard]
  ring

theorem star_factor (j : Jet K) (u : K) :
    j.second (2-u)-j.second u = (2-u-u)*j.starGuard := by
  simp only [Jet.second,Jet.starGuard]
  ring

/-- The explicit fixed 3-by-2 Sylvester resultant. -/
def res32 (A B C D L M N : K) : K :=
  A^2*N^3-A*B*M*N^2-2*A*C*L*N^2+A*C*M^2*N+3*A*D*L*M*N-A*D*M^3+
  B^2*L*N^2-B*C*L*M*N-2*B*D*L^2*N+B*D*L*M^2+C^2*L^2*N-C*D*L^2*M+D^2*L^3

/-- The actual common-root implication, proved without division by a
leading coefficient or even a degree assumption. -/
theorem res32_zero_of_common_root (A B C D L M N u : K)
    (hp : A*u^3+B*u^2+C*u+D=0) (hq : L*u^2+M*u+N=0) :
    res32 A B C D L M N=0 := by
  unfold res32
  linear_combination
    ((A*L^2*N-A*L*M^2+B*L^2*M-C*L^3)*u +
      (2*A*L*M*N-A*M^3-B*L^2*N+B*L*M^2-C*L^2*M+D*L^3))*hp +
    ((-A^2*L*N+A^2*M^2-A*B*L*M+A*C*L^2)*u^2 +
      (-A^2*M*N+A*B*M^2-A*D*L^2-B^2*L*M+B*C*L^2)*u +
      (A^2*N^2-A*B*M*N-2*A*C*L*N+A*C*M^2+A*D*L*M+B^2*L*N-B*C*L*M-B*D*L^2+C^2*L^2))*hq

def frontResiduePoly (h : K) : K := 7*h^3+6*h^2-3*h-3
def reverseResiduePoly (h : K) : K := -4*h^3-6*h^2+6*h+1
def comparedResiduePoly (h : K) : K := -8*h^3+6*h^2+2*h+1

/-- An integer polynomial congruence, so the residue proof is an identity
in the polynomial ring, not simply equality of functions on 17 points. -/
theorem front_mod_congruence (h : K) :
    res32 (-4) 7 (-8) 5 (-1-2*h) (4*h) (-1+2*h) =
    frontResiduePoly h+17*(137*h^3-86*h^2+11*h-1) := by
  unfold res32 frontResiduePoly
  ring

theorem reverse_mod_congruence (h : K) :
    res32 (-6) (-8) (-6) 7 (-1-7*h) (-1-3*h) (4+7*h) =
    reverseResiduePoly h+17*(1707*h^3+2667*h^2+1135*h+186) := by
  unfold res32 reverseResiduePoly
  ring

theorem mobius_mod_congruence (h : K) :
    -4*(-h)^3-6*(-h)^2*(1+14*h)+6*(-h)*(1+14*h)^2+(1+14*h)^3 =
    comparedResiduePoly h+17*(88*h^3+24*h^2+2*h) := by
  unfold comparedResiduePoly
  ring

theorem bezout_mod_congruence (h : K) :
    (-6*h^2+7*h-6)*frontResiduePoly h+(-h^2+3*h)*comparedResiduePoly h =
    1+17*(-2*h^5-h^4+2*h^3-2*h^2+1) := by
  unfold frontResiduePoly comparedResiduePoly
  ring

end Algebra

/-- The normalized second and third row equations pay the cubic, with
no division by the physical neighboring tap or the tap cubic. -/
theorem cubic_of_actual_arithmetic {K : Type*} [Field K] [CharZero K]
    (j : Jet K) (u h t : K) (hu : u≠0) (hk : kap u≠0)
    (hs : j.second u=j.p*kap u*h) (ht : t*tapCubic u=2*u*(3*u-2))
    (hf : j.value (2*u)=(kap (2*u)+2*t*u)*(j.p+2*u*j.p*h)) :
    j.cubic u=0 := by
  have z : tapCubic u*kap u*j.value (2*u)-
      (tapCubic u*kap (2*u)+4*u^2*(3*u-2))*(j.p*kap u+2*u*j.second u)=0 := by
    rw [hf,hs]
    linear_combination (2*u*kap u*(j.p+2*u*j.p*h))*ht
  rw [arithmetic_factor] at z
  exact (mul_eq_zero.mp z).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hu)) hk)

section GoodPrime

variable {K : Type*} [Field K]

def gamma (a : K) : K := (4+35*a*(1-a))/72

/-- Actual Taylor jets of X ↦ Πₐ(γ(1+X)), in ascending degree. -/
def gaussJet (a : K) : Jet K :=
  let g := gamma a
  let q0 := a^3-2*a^2+9*a/7-2/7
  let q1 := a^2-2*a+9/7
  let q2 := a-2
  ⟨g^3+q2*g^2+q1*g+q0, g*(3*g^2+2*q2*g+q1),
    g^2*(3*g+q2),g^3⟩

def gaussQuartic70 (a : K) : K := 70*a^4-140*a^3+90*a^2-20*a+1

end GoodPrime

instance mod17Prime : Fact (Nat.Prime 17) := ⟨by decide⟩

theorem two_jet_values_mod17 :
    gaussQuartic70 (7 : ZMod 17)=0 ∧ gaussQuartic70 (11 : ZMod 17)=0 ∧
    gamma (7 : ZMod 17)=16 ∧ gamma (11 : ZMod 17)=16 ∧
    (gamma (7 : ZMod 17))⁻¹-2=14 ∧
    gaussJet (7 : ZMod 17)=⟨15,12,2,16⟩ ∧
    gaussJet (11 : ZMod 17)=⟨10,7,6,16⟩ := by
  decide +kernel

theorem two_cubic_values_mod17 :
    (gaussJet (7 : ZMod 17)).starGuard=15 ∧
    (gaussJet (11 : ZMod 17)).starGuard=14 ∧
    (gaussJet (7 : ZMod 17)).cubicCoeffs=(-4,7,-8,5) ∧
    (gaussJet (11 : ZMod 17)).cubicCoeffs=(-6,-8,-6,7) := by
  decide +kernel

theorem residue_no_common_slope {K : Type*} [Field K] [CharP K 17]
    (h : K) (hf : frontResiduePoly h=0) (hc : comparedResiduePoly h=0) : False := by
  have hz := bezout_mod_congruence h
  have pz : (17:K)=0 := CharP.cast_eq_zero K 17
  simp only [hf,hc,pz,mul_zero,zero_mul,add_zero] at hz
  exact zero_ne_one hz

end RKCert.ReviewedNative.SDIRK8SingletonSlopeReceipts
