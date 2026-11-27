module
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

@[expose] public section

/-! # An integral-reciprocal-diagonal obstruction in the relaxed SDIRK7 chart
The scalar theorem is over Q, for every nonzero integer reciprocal diagonal.
It is not a global lower bound on rational nine-stage strict tableaux. -/

namespace RKResearch.Certified.SDIRKSevenZeroFirstCurve

def P6 {R : Type*} [Ring R] (z : R) : R :=
  z^6-30*z^5+405*z^4-3190*z^3+14400*z^2-31500*z+25725

def Q4 {R : Type*} [Ring R] (z : R) : R :=
  z^4-24*z^3+180*z^2-480*z+360

def a (z : ℚ) : ℚ := 1*z^10 - 56*z^9 + 1364*z^8 - 18970*z^7 + 166400*z^6 - 959880*z^5 + 3682050*z^4 - 9267600*z^3 + 14641200*z^2 - 13104000*z + 5040000
def b (z : ℚ) : ℚ := -6*z^10 + 314*z^9 - 7086*z^8 + 90440*z^7 - 720590*z^6 + 3735540*z^5 - 12741000*z^4 + 28231200*z^3 - 38934000*z^2 + 30240000*z - 10080000
def c (z : ℚ) : ℚ := 9*z^10 - 438*z^9 + 9102*z^8 - 105870*z^7 + 760610*z^6 - 3519960*z^5 + 10628400*z^4 - 20727600*z^3 + 25099200*z^2 - 17136000*z + 5040000

theorem discriminant (z : ℚ) :
    (b z)^2-4*a z*c z = (2*z^2*Q4 z)^2*P6 z := by
  unfold a b c P6 Q4
  ring

def L₀ (z u : ℚ) : ℚ := (1 / 21600)*z^8*u - (1 / 7200)*z^8 - (1 / 1080)*z^7*u + (1 / 432)*z^7 + (1 / 144)*z^6*u - (1 / 72)*z^6 - (1 / 45)*z^5*u + (1 / 30)*z^5 + (1 / 36)*z^4*u - (1 / 36)*z^4
def L₁ (z u : ℚ) : ℚ := (1 / 21600)*z^9*u - (1 / 7200)*z^9 - (1 / 900)*z^8*u + (31 / 10800)*z^8 + (11 / 1080)*z^7*u - (47 / 2160)*z^7 - (31 / 720)*z^6*u + (13 / 180)*z^6 + (1 / 12)*z^5*u - (19 / 180)*z^5 - (1 / 18)*z^4*u + (1 / 18)*z^4
def L₂ (z u : ℚ) : ℚ := (1 / 30240)*z^10*u - (1 / 10080)*z^10 - (31 / 37800)*z^9*u + (163 / 75600)*z^9 + (577 / 75600)*z^8*u - (91 / 5400)*z^8 - (41 / 1260)*z^7*u + (143 / 2520)*z^7 + (23 / 360)*z^6*u - (1 / 12)*z^6 - (2 / 45)*z^5*u + (2 / 45)*z^5

theorem chronological_resultant (z u : ℚ) :
    L₁ z u ^ 2-L₀ z u*L₂ z u =
      (1/1632960000) * z^8 * (a z*u^2+b z*u+c z) := by
  unfold L₀ L₁ L₂ a b c
  ring

private def f (t : ℤ) : ℤ :=
  t^6+30*t^4-90*t^3-825*t^2+750*t+4475

private def g (t : ℤ) : ℤ := t^3+15*t-45
private def r (t : ℤ) : ℤ := 1050*t^2-2100*t-2450

private theorem complete_square (t : ℤ) : f t = (g t)^2-r t := by
  unfold f g r
  ring

private theorem center (z : ℤ) : P6 z = f (z-5) := by
  unfold P6 f
  ring

private theorem right_gap (t : ℤ) (ht : 600≤t) :
    0 < r t ∧ r t < 2*|g t|-1 := by
  have ht0 : 0 ≤ t := by omega
  have ht2 : 0 ≤ t * (t-600) := mul_nonneg ht0 (by omega)
  have ht3 : 0 ≤ t^2 * (t-600) := mul_nonneg (sq_nonneg _) (by omega)
  have g0 : 0 ≤ g t := by unfold g; nlinarith
  rw [abs_of_nonneg g0]
  unfold r g
  constructor <;> nlinarith

private theorem left_gap (t : ℤ) (ht : t≤-600) :
    0 < r t ∧ r t < 2*|g t|-1 := by
  let s := -t
  have st : s ≥ 600 := by dsimp [s]; omega
  have h0 : 0≤s := by omega
  have h2 : 0≤s*(s-600) := mul_nonneg h0 (by omega)
  have h3 : 0≤s^2*(s-600) := mul_nonneg (sq_nonneg _) (by omega)
  have he : t = -s := by simp [s]
  rw [he]
  have gn : g (-s) ≤ 0 := by unfold g; nlinarith
  rw [abs_of_nonpos gn]
  unfold r g
  constructor <;> nlinarith

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 16000 in
private theorem small_check : ∀ i : Fin 1201,
    let d := (f ((i.val : ℤ)-600)).natAbs
    (Nat.sqrt d)^2 ≠ d := by
  decide +kernel

private theorem no_in_between {b y : ℤ}
    (low : (b-1)^2 < y^2) (high : y^2 < b^2) (hb : 0≤b) : False := by
  have hp : 0 ≤ |y| := abs_nonneg _
  have hSq : |y|^2=y^2 := sq_abs _
  by_cases h : |y|<b
  · have br : |y|≤b-1 := by omega
    have non : 0≤b-1-|y| := by omega
    have other : 0≤b-1+|y| := by omega
    have sum := mul_nonneg non other
    nlinarith
  · have non : 0≤|y|-b := by omega
    have other : 0≤|y|+b := by omega
    have sum := mul_nonneg non other
    nlinarith

private theorem no_square_centered (t y : ℤ) (e : y^2=f t) : False := by
  have large (h : 0<r t ∧ r t < 2*|g t|-1) : False := by
    have eq : y^2=|g t|^2-r t := by rw [sq_abs,←complete_square,e]
    apply no_in_between (b:=|g t|) (y:=y) _ _ (abs_nonneg _)
    · nlinarith [h.2]
    · linarith [h.1]
  by_cases h : 600≤t
  · exact large (right_gap _ h)
  by_cases h' : t≤-600
  · exact large (left_gap _ h')
  let i : Fin 1201 := ⟨(t+600).toNat,by omega⟩
  have eq : (i.val:ℤ)-600=t := by dsimp [i]; omega
  have en := congrArg Int.natAbs e
  rw [Int.natAbs_pow] at en
  have eq' := small_check i
  change (Nat.sqrt (f ((i.val:ℤ)-600)).natAbs)^2 ≠ (f ((i.val:ℤ)-600)).natAbs at eq'
  rw [eq,←en,Nat.sqrt_eq'] at eq'
  exact eq' rfl

/-- This genus-two curve has no affine rational point with integral
nonzero or zero first coordinate. The denominators of the second
coordinate are unrestricted. -/
theorem no_square_integral (z : ℤ) : ¬ IsSquare (P6 (z:ℚ)) := by
  have eq : P6 (z:ℚ) = ((P6 z : ℤ):ℚ) := by push_cast [P6]; rfl
  rw [eq,Rat.isSquare_intCast_iff]
  rintro ⟨y,hy⟩
  rw [center] at hy
  exact no_square_centered _ _ (by simpa only [pow_two] using hy.symm)

private theorem Q4_mod13 : ∀ i : Fin 13, Q4 ((i.val:ℕ):ZMod 13) ≠ 0 := by
  decide +kernel

theorem Q4_ne_zero (z : ℤ) : Q4 (z:ℚ) ≠ 0 := by
  have hmod (x : ZMod 13) : Q4 x ≠ 0 := by
    let i : Fin 13 := ⟨x.val,x.val_lt⟩
    simpa only [i,ZMod.natCast_zmod_val] using Q4_mod13 i
  intro h
  have e : Q4 z = 0 := by exact_mod_cast (show ((Q4 z : ℤ):ℚ)=0 from by
    simpa only [Q4,Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_pow,Int.cast_ofNat] using h)
  apply hmod (z:ZMod 13)
  have e' := congrArg (Int.castRingHom (ZMod 13)) e
  simpa only [Q4,map_sub,map_add,map_mul,map_pow,map_ofNat,map_zero,Int.coe_castRingHom] using e'

theorem no_rational_chronological_root_integral (z : ℤ) (hz : z≠0) (u : ℚ) :
    a (z:ℚ)*u^2+b (z:ℚ)*u+c (z:ℚ) ≠ 0 := by
  let v := (z:ℚ)
  have vz : v ≠ 0 := by change (z:ℚ) ≠ 0; exact_mod_cast hz
  have dv : 2*v^2*Q4 v ≠ 0 := mul_ne_zero (mul_ne_zero (by decide) (pow_ne_zero 2 vz)) (Q4_ne_zero z)
  intro eq
  change a v*u^2+b v*u+c v=0 at eq
  have square : (2*a v*u+b v)^2 = (2*v^2*Q4 v)^2*P6 v := by
    linear_combination 4*a v*eq + discriminant v
  apply no_square_integral z
  refine ⟨(2*a v*u+b v)/(2*v^2*Q4 v),?_⟩
  change P6 v = _
  rw [←pow_two,div_pow]
  exact (eq_div_iff (pow_ne_zero 2 dv)).mpr (by simpa only [mul_comm (P6 v)] using square.symm)

theorem no_integral_reciprocal_zero_first_moments (z : ℤ) (hz : z≠0) (u : ℚ) :
    L₁ (z:ℚ) u^2 ≠ L₀ (z:ℚ) u*L₂ (z:ℚ) u := by
  intro e
  have er := chronological_resultant (z:ℚ) u
  rw [e,sub_self] at er
  have zq : (z:ℚ)≠0 := by exact_mod_cast hz
  have non : ((1/1632960000) : ℚ) * (z:ℚ)^8 ≠ 0 := mul_ne_zero (by decide +kernel) (pow_ne_zero 8 zq)
  exact no_rational_chronological_root_integral z hz u
    ((mul_eq_zero.mp er.symm).resolve_left non)

end RKResearch.Certified.SDIRKSevenZeroFirstCurve
