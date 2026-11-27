module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.CharZero.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Scalar identities for an opposite-residual reflected order-eight star -/

namespace RKResearch.Certified.SDIRKEightAntireflectedStar

section Field
variable {K : Type*} [Field K] [CharZero K]

def legendre₄ (m t : K) : K := t^4 - 6*m^2*t^2/7 + 3*m^4/35
def starMean (m v : K) : K :=
  (2-m)^4 + 6*(2-m)^2*v + v^2 - 6*m^2*((2-m)^2+v)/7 + 3*m^4/35
def starDifference (m v : K) : K :=
  4*(2-m)*((2-m)^2+v) - 12*m^2*(2-m)/7

theorem star_u_fit {m v a b : K}
    (ha : a*((2-v)/2)=starDifference m v)
    (hb : b=4*legendre₄ m (1-m)-2*a*(1-m))
    (hme : starMean m v=((2-v)/2)*(a*(2-m)+b*((2-v)/2))) :
    (v-1)*((2*m^4-20*m^3+80*m^2-140*m+70)*v+
      (14*m^4-140*m^3+420*m^2-420*m+105))=0 := by
  have id : starMean m v-starDifference m v*(2-m)
      -4*((2-v)/2)^2*legendre₄ m (1-m)+
      2*((2-v)/2)*(1-m)*starDifference m v=
      -(4/35)*((v-1)*((2*m^4-20*m^3+80*m^2-140*m+70)*v+
        (14*m^4-140*m^3+420*m^2-420*m+105))) := by
    unfold starMean starDifference legendre₄
    ring
  have z : starMean m v-starDifference m v*(2-m)
      -4*((2-v)/2)^2*legendre₄ m (1-m)+
      2*((2-v)/2)*(1-m)*starDifference m v=0 := by
    rw [←ha, hme, hb]
    ring
  rw [z] at id
  linear_combination (35/4 : K)*id

theorem fourth_recovery {x g k : K} (hk : k ≠ 0)
    (eq : -(x^3)/6+3*x^2/2-3*x+1+g*(4/3-(k+4)*(x-1)/(3*k))=0) :
    2*(4*k-(k+4)*(x-1))*g=k*(x^3-9*x^2+18*x-6) := by
  field_simp at eq
  linear_combination (1/6 : K)*eq

end Field

theorem projection_pivot {R : Type*} [CommRing R]
    {t g a b d e f ℓ n : R}
    (hu : ℓ-g*(a*t+b*g)=0)
    (hv : t*(t^2-n)-g*(d+e*t^2+f*t*g)=0) :
    g*(b*(d+e*t^2)-f*a*t^2)=t*(b*(t^2-n)-f*ℓ) := by
  linear_combination f*t*hu-b*hv

theorem reflected_opener {R : Type*} [CommRing R] {m : R}
    (h : 2*m^2-6*m+3=0) : (2*m-3)^2=3 := by
  linear_combination 2*h

theorem fifth_norm_guard {R : Type*} [CommRing R] {d a b t : R}
    (ht : t^2=d) (hn : a^2-d*b^2 ≠ 0) : a+t*b ≠ 0 := by
  intro h
  apply hn
  calc
    a^2-d*b^2=(a+t*b)*(a-t*b) := by rw [←ht]; ring
    _=0 := by rw [h, zero_mul]

end RKResearch.Certified.SDIRKEightAntireflectedStar
