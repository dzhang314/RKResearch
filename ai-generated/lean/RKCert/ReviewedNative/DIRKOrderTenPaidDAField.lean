module

public import Lean

@[expose] public section

/-! # Field algebra of the compensated three-column DA test

The tableau/rank argument supplies the weighted moments and an affine
paid DA read. This module handles the field algebra independently of
actual tableau coefficients or a sign structure. -/
namespace RKResearch.Certified.Graded.PaidDAField

open Lean.Grind

section
variable {K : Type} [Field K]

theorem shift_cancel (u v k : K) (hu : u ≠ 0) (hv : v-u ≠ 0) :
    let d := k/(u*(v-u))
    d*u = k/(v-u) ∧
    d*u^2 - k*v/(v-u) = -k ∧
    d*u^3 - k*v^2/(v-u)+(v-u/2)*k = -(u+u/2)*k := by
  dsimp
  have iu := Field.mul_inv_cancel hu
  have iv := Field.mul_inv_cancel hv
  simp only [Field.div_eq_mul_inv, Field.inv_mul]
  constructor
  · grind
  constructor
  · grind
  · grind

theorem tapOne (u a S : K) (hu : u ≠ 0) (h : a*u = S) :
    a = S/u := by
  have iu := Field.mul_inv_cancel hu
  simp only [Field.div_eq_mul_inv]
  rw [←h]
  grind

private theorem nonzeroMul (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    x*y ≠ 0 := by
  intro h
  have ix := Field.mul_inv_cancel hx
  have he := congrArg (fun z => z*x⁻¹) h
  have ha : x*y*x⁻¹ = y*(x*x⁻¹) := by grind
  rw [ha, ix, Semiring.mul_one, Semiring.zero_mul] at he
  exact hy he

theorem tapTwo (u v a b S T : K) (hu : u ≠ 0) (hv : u-v ≠ 0)
    (hS : a*u+b*v=S) (hT : a*u^2+b*v^2=T) :
    a=(T-v*S)/(u*(u-v)) := by
  have h : a*(u*(u-v)) = T-v*S := by rw [←hS,←hT]; grind
  have hi := Field.mul_inv_cancel (nonzeroMul u (u-v) hu hv)
  simp only [Field.div_eq_mul_inv]
  rw [←h, Semiring.mul_assoc, hi, Semiring.mul_one]

theorem tapThree (u v w a b c S T R : K) (hu : u ≠ 0) (hv : u-v ≠ 0) (hw : u-w ≠ 0)
    (hS : a*u+b*v+c*w=S) (hT : a*u^2+b*v^2+c*w^2=T) (hR : a*u^3+b*v^3+c*w^3=R) :
    a=(R-(v+w)*T+v*w*S)/(u*(u-v)*(u-w)) := by
  have h : a*(u*(u-v)*(u-w)) = R-(v+w)*T+v*w*S := by rw [←hS,←hT,←hR]; grind
  have hi := Field.mul_inv_cancel (nonzeroMul _ (u-w) (nonzeroMul u (u-v) hu hv) hw)
  simp only [Field.div_eq_mul_inv]
  rw [←h, Semiring.mul_assoc, hi, Semiring.mul_one]

theorem weightedShift (kU kW kR k a b c u v : K) (hk : k ≠ 0) :
    (kU*(a+k/(u*(v-u)))+kW*b+kR*c)/k =
      (kU*a+kW*b+kR*c)/k+kU/(u*(v-u)) := by
  have hk' := Field.mul_inv_cancel hk
  simp only [Field.div_eq_mul_inv]
  grind

def affineDefect (u w r a b c : K) : K :=
  (w-r)*a+(r-u)*b+(u-w)*c

theorem affineDefect_addShift (u w r a b c d : K) :
    affineDefect u w r (a+d) (b+d) (c+d) = affineDefect u w r a b c := by
  unfold affineDefect
  grind

theorem affineDefect_of_affine (u w r a b : K) :
    affineDefect u w r (a+b*u) (a+b*w) (a+b*r) = 0 := by
  unfold affineDefect
  grind

def m1 (s : K) : K := s^2/2
def m2 (s k : K) : K := s^3/3-k
def m3 (u s k : K) : K := s^4/4-(u+u/2)*k

def fixedTapTwo (u v S T : K) : K := (T-v*S)/(u*(u-v))
def fixedTapThree (u v w S T R : K) : K := (R-(v+w)*T+v*w*S)/(u*(u-v)*(u-w))

def fixedReadW (u w kU kW : K) : K :=
  (kU*fixedTapTwo u w (m1 w) (m2 w kW) + kW*fixedTapTwo w u (m1 w) (m2 w kW))/kW

def fixedReadR (u w r kU kW kR : K) : K :=
  (kU*fixedTapThree u w r (m1 r) (m2 r kR) (m3 u r kR)
  + kW*fixedTapThree w u r (m1 r) (m2 r kR) (m3 u r kR)
  + kR*fixedTapThree r u w (m1 r) (m2 r kR) (m3 u r kR))/kR

def fixedDefect (u w r kU kW kR : K) : K :=
  affineDefect u w r (u/2) (fixedReadW u w kU kW) (fixedReadR u w r kU kW kR)

/-- Once the common dirty-tap shift has been made, the six actual
ordinary taps cannot satisfy both the moment targets and an affine DA
read when the fixed-clock determinant is nonzero. -/
theorem not_affine_compensated (u w r kU kW kR au aw1 aw2 ar1 ar2 ar3 : K)
    (hu : u ≠ 0) (hw : w ≠ 0) (hr : r ≠ 0)
    (huw : u-w ≠ 0) (hwu : w-u ≠ 0) (hur : u-r ≠ 0) (hru : r-u ≠ 0)
    (hwr : w-r ≠ 0) (hrw : r-w ≠ 0)
    (hU : au*u=m1 u)
    (hW1 : aw1*u+aw2*w=m1 w) (hW2 : aw1*u^2+aw2*w^2=m2 w kW)
    (hR1 : ar1*u+ar2*w+ar3*r=m1 r)
    (hR2 : ar1*u^2+ar2*w^2+ar3*r^2=m2 r kR)
    (hR3 : ar1*u^3+ar2*w^3+ar3*r^3=m3 u r kR)
    (hA : ∃ a b : K, au=a+b*u ∧
      (kU*aw1+kW*aw2)/kW=a+b*w ∧ (kU*ar1+kW*ar2+kR*ar3)/kR=a+b*r)
    (hF : fixedDefect u w r kU kW kR ≠ 0) : False := by
  have eau : au=u/2 := by
    have he := tapOne u au (m1 u) hu hU
    have iu := Field.mul_inv_cancel hu
    rw [he]
    simp only [m1, Field.div_eq_mul_inv]
    clear hU hW1 hW2 hR1 hR2 hR3 hA hF he
    grind
  have ew1 := tapTwo u w aw1 aw2 (m1 w) (m2 w kW) hu huw hW1 hW2
  have ew2 := tapTwo w u aw2 aw1 (m1 w) (m2 w kW) hw hwu
    (by simpa [Semiring.add_comm] using hW1) (by simpa [Semiring.add_comm] using hW2)
  have er1 := tapThree u w r ar1 ar2 ar3 (m1 r) (m2 r kR) (m3 u r kR) hu huw hur hR1 hR2 hR3
  have er2 := tapThree w u r ar2 ar1 ar3 (m1 r) (m2 r kR) (m3 u r kR) hw hwu hwr
    (by rw [Semiring.add_comm (ar2*w) (ar1*u)]; exact hR1)
    (by rw [Semiring.add_comm (ar2*w^2) (ar1*u^2)]; exact hR2)
    (by rw [Semiring.add_comm (ar2*w^3) (ar1*u^3)]; exact hR3)
  have er3 := tapThree r u w ar3 ar1 ar2 (m1 r) (m2 r kR) (m3 u r kR) hr hru hrw
    (by rw [Semiring.add_assoc, Semiring.add_comm (ar3*r)]; exact hR1)
    (by rw [Semiring.add_assoc, Semiring.add_comm (ar3*r^2)]; exact hR2)
    (by rw [Semiring.add_assoc, Semiring.add_comm (ar3*r^3)]; exact hR3)
  rcases hA with ⟨a,b,hAU,hAW,hAR⟩
  apply hF
  unfold fixedDefect fixedReadW fixedReadR fixedTapTwo fixedTapThree
  rw [←eau,←ew1,←ew2,←er1,←er2,←er3,hAU,hAW,hAR]
  exact affineDefect_of_affine u w r a b

end
end RKResearch.Certified.Graded.PaidDAField
