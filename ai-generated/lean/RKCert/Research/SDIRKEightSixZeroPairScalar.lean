import Mathlib.Tactic.Ring.Basic

/-!
Literal paid scalar steps for the six-zero two-clock pair boundary. These
theorems take the scalar gates as hypotheses; rooted ingress is separate.
-/

namespace RKResearch.Certified.SDIRKEightSixZeroPairScalar

variable {R : Type*} [CommRing R]

def gap (v : R) : R := 4*v^3-12*v^2+3*v+2
def sameRead (v : R) : R := -4*v^3+30*v+4
def oppositeRead (v : R) : R := -16*v^3+36*v+4

theorem literal_first_tap {p q v w : R} (h : p+q=w)
    (hg : 1+2*w-w^2+2*q*v=0) :
    2*p*v = 2*w*v+1+2*w-w^2 := by
  calc
    _ = 2*w*v+1+2*w-w^2 + 2*v*(p+q-w) - (1+2*w-w^2+2*q*v) := by ring1
    _ = _ := by rw [h,hg]; ring1

variable [IsDomain R]

theorem same_gap_obstruction {v : R} (h2 : (2:R) ≠ 0) (h3 : (3:R) ≠ 0)
    (h : gap v = 0) (hr : sameRead v = 0) : False := by
  have hh : 4*v^2-11*v-2 = 0 := by
    apply (mul_eq_zero.mp (_ : (3:R)*(4*v^2-11*v-2) = 0)).resolve_left h3
    calc
      _ = -(gap v + sameRead v) := by unfold gap sameRead; ring1
      _ = _ := by rw [h,hr]; ring1
  have hl : 3*v+2 = 0 := by
    apply (mul_eq_zero.mp (_ : (3:R)*(3*v+2) = 0)).resolve_left h3
    calc
      _ = 4*gap v+(1-4*v)*(4*v^2-11*v-2) := by unfold gap; ring1
      _ = _ := by rw [h,hh]; ring1
  have hz : (64:R)=0 := by
    calc
      _ = 9*(4*v^2-11*v-2)-(3*v+2)*(12*v-41) := by ring1
      _ = _ := by rw [hh,hl]; ring1
  exact (pow_ne_zero 6 h2) ((show (2:R)^6=64 by ring1).trans hz)

theorem opposite_gap_obstruction {v : R} (h2 : (2:R) ≠ 0)
    (h : gap v = 0) (hneg : gap (-v) = 0) (hr : oppositeRead v = 0) : False := by
  have h4 : (4:R) ≠ 0 := by
    rw [show (4:R)=(2:R)^2 by ring1]
    exact pow_ne_zero 2 h2
  have hs : 1-6*v^2=0 := by
    apply (mul_eq_zero.mp (_ : (4:R)*(1-6*v^2)=0)).resolve_left h4
    calc
      _ = gap v + gap (-v) := by unfold gap; ring1
      _ = _ := by rw [h,hneg]; ring1
  have hv : v ≠ 0 := by
    intro hz
    simp [hz] at hs
  have hd : 4*v^2+3=0 := by
    apply (mul_eq_zero.mp (_ : (2:R)*v*(4*v^2+3)=0)).resolve_left (mul_ne_zero h2 hv)
    calc
      _ = gap v - gap (-v) := by unfold gap; ring1
      _ = _ := by rw [h,hneg]; ring1
  have hi : 12*v+1=0 := by
    apply (mul_eq_zero.mp (_ : (4:R)*(12*v+1)=0)).resolve_left h4
    calc
      _ = oppositeRead v + 2*(gap v-gap (-v)) := by unfold oppositeRead gap; ring1
      _ = _ := by rw [h,hneg,hr]; ring1
  have h11 : (11:R)=0 := by
    calc
      _ = 3*(4*v^2+3)+2*(1-6*v^2) := by ring1
      _ = _ := by rw [hd,hs]; ring1
  have h23 : (23:R)=0 := by
    calc
      _ = (12*v+1)*(12*v-1)+24*(1-6*v^2) := by ring1
      _ = _ := by rw [hi,hs]; ring1
  exact one_ne_zero (calc
    (1:R) = 23-2*11 := by ring1
    _ = 0 := by rw [h11,h23]; ring1)

end RKResearch.Certified.SDIRKEightSixZeroPairScalar
