module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8HalfQuadraticReceipts

open scoped BigOperators

/-- Vandermonde-cleared evaluation of the three strict taps to the
earlier zero sites on an arbitrary profile. -/
theorem threeTapRead {R : Type*} [CommRing R]
    (a b s u v w fa fb fs m0 m1 m2 : R)
    (h0 : u+v+w=m0) (h1 : a*u+b*v+s*w=m1)
    (h2 : a^2*u+b^2*v+s^2*w=m2) :
    (a-b)*(a-s)*(b-s)*(u*fa+v*fb+w*fs) =
      (b-s)*(m2-(b+s)*m1+b*s*m0)*fa+
      (s-a)*(m2-(a+s)*m1+a*s*m0)*fb+
      (a-b)*(m2-(a+b)*m1+a*b*m0)*fs := by
  rw [← h0, ← h1, ← h2]
  ring

/-- Elimination of an unknown literal row-five defect from two affine
rank conditions, without choosing a pivot. -/
theorem affineReadElim {R : Type*} [CommRing R] (A B C D h : R)
    (hA : A+B*h=0) (hC : C+D*h=0) : A*D-B*C=0 := by
  calc
    A*D-B*C = D*(A+B*h)-B*(C+D*h) := by ring
    _ = 0 := by rw [hA,hC]; ring

/-- Determinant of the three-by-three scalar Hankel matrix. -/
def hankel3 {R : Type*} [CommRing R] (m0 m1 m2 m3 m4 : R) : R :=
  m0*m2*m4+2*m1*m2*m3-m0*m3^2-m1^2*m4-m2^3

/-- After multiplying the sampled moments by six literal nodal factors,
six of eight physical rows contribute zero. Their clocks need not be
distinct. The remaining Hankel determinant vanishes without dividing
by the difference of the last two clocks or by either weight. -/
theorem sixPeggedHankel {R : Type*} [CommRing R]
    (x w : Fin 6 → R) (a b wa wb : R) :
    let P := fun y ↦ ∏ i : Fin 6, (y-x i)
    let m := fun j : ℕ ↦
      (∑ i : Fin 6, w i * P (x i) * (x i)^j) +
        wa * P a * a^j + wb * P b * b^j
    hankel3 (m 0) (m 1) (m 2) (m 3) (m 4) = 0 := by
  dsimp
  have hp (i : Fin 6) : (∏ k : Fin 6, (x i - x k)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
  simp only [hp,mul_zero,zero_mul,Finset.sum_const_zero,zero_add,pow_zero,mul_one]
  unfold hankel3
  ring

end RKCert.ReviewedNative.SDIRK8HalfQuadraticReceipts
