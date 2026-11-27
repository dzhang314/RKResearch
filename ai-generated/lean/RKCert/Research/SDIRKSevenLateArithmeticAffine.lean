module

public import RKCert.Research.SDIRKSevenLateGhostScalar
public import RKCert.Research.SDIRKSevenDirtyArithmeticAtlas
public import RKCert.Research.SDIRKSevenPairedClean
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Scalar reduction of the arithmetic late-ghost affine-helper chart -/

namespace RKResearch.Certified.SDIRKSevenLateArithmeticAffine
open SDIRKSevenDirtyArithmeticAtlas

def hDen (u : ℚ) : ℚ := u^5-11*u^4+42*u^3-62*u^2+34*u-6
def hNum (u : ℚ) : ℚ := 5*u^5-46*u^4+148*u^3-191*u^2+90*u-12

private def hom {R : Type*} [CommRing R] (a b : R) : R :=
  a^5-11*a^4*b+42*a^3*b^2-62*a^2*b^3+34*a*b^4-6*b^5

set_option maxRecDepth 8192 in
private theorem finite_h : ∀ a b : Fin 5,
    hom (a.val : ZMod 5) (b.val : ZMod 5)=0 →
      (a.val : ZMod 5)=0 ∧ (b.val : ZMod 5)=0 := by decide +kernel

theorem pin_den_ne (x : ℚ) : hDen x≠0 := by
  intro e
  have hd : (x.den : ℚ)≠0 := by exact_mod_cast x.den_nz
  have scale : x*(x.den : ℚ)=(x.num : ℚ) := by
    nth_rw 1 [←x.num_div_den]
    exact div_mul_cancel₀ _ hd
  have hx : hom (x.num : ℚ) (x.den : ℚ)=(x.den : ℚ)^5*hDen x := by
    rw [←scale]
    simp only [hom,hDen]
    ring
  rw [e,mul_zero] at hx
  have hz : hom x.num (x.den : ℤ)=0 := by
    apply Int.cast_injective (α := ℚ)
    simpa only [hom,Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,
      Int.cast_natCast,Int.cast_zero] using hx
  have hp := congrArg (Int.castRingHom (ZMod 5)) hz
  have h₅ : hom (x.num : ZMod 5) (x.den : ZMod 5)=0 := by
    simp only [hom,map_add,map_sub,map_mul,map_pow,map_ofNat,map_zero,map_natCast] at hp
    simpa only [hom,Int.coe_castRingHom] using hp
  let a : ZMod 5 := x.num
  let b : ZMod 5 := x.den
  have hv : hom (a.val : ZMod 5) (b.val : ZMod 5)=0 := by
    simpa only [ZMod.natCast_zmod_val] using h₅
  obtain ⟨ha,hb⟩ := finite_h ⟨a.val,a.val_lt⟩ ⟨b.val,b.val_lt⟩ hv
  have han : (5:ℕ) ∣ x.num.natAbs := by
    have h : (x.num : ZMod 5)=0 := by simpa only [ZMod.natCast_zmod_val,a] using ha
    simpa using (Int.natAbs_dvd_natAbs.mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd x.num 5).mp h))
  have hbn : (5:ℕ) ∣ x.den := by
    have h : (x.den : ZMod 5)=0 := by simpa only [ZMod.natCast_zmod_val,b] using hb
    exact (ZMod.natCast_eq_zero_iff x.den 5).mp h
  have bad := Nat.dvd_gcd han hbn
  rw [x.reduced.gcd_eq_one] at bad
  exact (by decide : ¬ (5:ℕ) ∣ 1) bad

theorem arithmetic_pin_identity (u h : ℚ) :
    Ehat u h=4*(hNum u-hDen u*h) := by
  simp only [Ehat,q₁,q₂,M,T,hNum,hDen]
  ring

theorem arithmetic_ghost_pin {u h : ℚ} (read : Ehat u h=0) :
    h=hNum u/hDen u := by
  apply (eq_div_iff (pin_den_ne u)).mpr
  rw [arithmetic_pin_identity] at read
  linear_combination -read/4

def S₀ (u : ℚ) : ℚ := (u-2)*(2*u^4-11*u^3+11*u^2+6*u-6)
def S₁ (u : ℚ) : ℚ := -(2*u^5-12*u^4-u^3+105*u^2-178*u+78)
def S₂ (u : ℚ) : ℚ := 3*(u-3)*(u-1)*(u^2-6*u+7)
def term (u i j k : ℚ) : ℚ := S₀ u*i+S₁ u*j+S₂ u*k

def K₁ (u i j k : ℚ) : ℚ := k-(3*u-1)*j+u*(2*u-1)*i
def Kᵤ (u i j k : ℚ) : ℚ := k-2*u*j+(2*u-1)*i
def Kᵥ (u i j k : ℚ) : ℚ := k-(u+1)*j+u*i
def arithThird (u : ℚ) : ℚ := 4*u^3-24*u^2+39*u-17

def terminalRaw (u i j k : ℚ) : ℚ :=
  (u-1)*((2*u-1)*hDen u-hNum u)*M u*arithThird u*Kᵥ u i j k
  -(2*u-2)*(u*hDen u-hNum u)*M u*T u*Kᵤ u i j k
  -(u-1)*(hDen u-hNum u)*T u*K₁ u i j k

set_option maxHeartbeats 4000000 in
/-- The terminal affine constraint simplifies to one fixed linear
form on the three early-cubic moments. -/
theorem terminal_identity (u i j k : ℚ) :
    terminalRaw u i j k=2*T u*(u-1)^3*M u*term u i j k := by
  simp only [terminalRaw,hDen,hNum,M,T,arithThird,K₁,Kᵤ,Kᵥ,term,S₀,S₁,S₂]
  ring

/-- At a singular two-equation hull pivot both Cramer numerators
must vanish, even though the solution is not assumed unique. -/
theorem singular_hull_compatibility {A₀ A₁ A₂ B₀ B₁ B₂ s p : ℚ}
    (en : A₂-s*A₁+p*A₀=0) (ex : B₂-s*B₁+p*B₀=0)
    (sing : A₁*B₀-A₀*B₁=0) :
    A₂*B₀-A₀*B₂=0 ∧ A₂*B₁-A₁*B₂=0 := by
  constructor
  · linear_combination B₀*en-A₀*ex+s*sing
  · linear_combination B₁*en-A₁*ex+p*sing

/-- The nominal affine tap pole cannot occur at a rational
distinct second-active clock if the actual compatibility holds. -/
theorem affine_den_ne {t x r : ℚ} (hx : x≠1)
    (read : SDIRKSevenLateGhostScalar.gap t x=r*SDIRKSevenLateGhostScalar.gap t 1) :
    SDIRKSevenLateGhostScalar.V x+r/2≠0 := by
  open SDIRKSevenLateGhostScalar in
  intro h
  simp only [helper_gap] at read
  have a : U 1=1/3 := by norm_num [U]
  have b : V 1= -1/2 := by norm_num [V]
  rw [a,b] at read
  simp only [U,V] at read h
  have g : (x-1)*(x^2-4*x+1)=0 := by
    linear_combination 3*read+(3*t+2)*h
  have q := (mul_eq_zero.mp g).resolve_left (sub_ne_zero.mpr hx)
  apply SDIRKSevenPairedClean.reverse_pair_impossible (u:=x)
  linear_combination q

end RKResearch.Certified.SDIRKSevenLateArithmeticAffine
