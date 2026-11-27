module

public import RKCert.ReviewedNative.CubicCubicQuadraticReplay
public import Mathlib.Algebra.Algebra.Rat

@[expose] public section

/-! Rational-coordinate interpretation of the same cubic/cubic/quadratic
reduction. All arithmetic correctness is by standard kernel theorems;
the target is any commutative ℚ-algebra, not necessarily a field. -/
namespace RKResearch.Certified.CubicCubicQuadraticRatReplay
open CubicCubicQuadraticReplay (Q2 Q3 a2 a3 m2 m3 v2 v3 v2_a2 v3_a3 v2_m2 v3_m3)

abbrev C3 := Q3 Rat
abbrev C9 := Q3 C3
abbrev C18 := Q2 C9

structure Reductions where
  inner : C3
  middle : C9
  outer : C18

def pack3 (q : Rat) : C3 := (q,0,0)
def pack9 (q : Rat) : C9 := (pack3 q,pack3 0,pack3 0)
def pack (q : Rat) : C18 := (pack9 q,pack9 0)
def add3 : C3 → C3 → C3 := a3 Rat.add
def add9 : C9 → C9 → C9 := a3 add3
def add : C18 → C18 → C18 := a2 add9
def mul3 (D : Reductions) : C3 → C3 → C3 := m3 Rat.add Rat.mul D.inner
def mul9 (D : Reductions) : C9 → C9 → C9 := m3 add3 (mul3 D) D.middle
def mul (D : Reductions) : C18 → C18 → C18 := m2 add9 (mul9 D) D.outer

variable {R : Type*} [CommRing R] [Algebra ℚ R]

def val3 (x : R) : C3 → R := v3 (algebraMap ℚ R) x
def val9 (x y : R) : C9 → R := v3 (val3 x) y
def val (x y z : R) : C18 → R := v2 (val9 x y) z

structure Roots (D : Reductions) (x y z : R) : Prop where
  inner : x^3 = val3 x D.inner
  middle : y^3 = val9 x y D.middle
  outer : z^2 = val x y z D.outer

@[simp] theorem val3_pack (x : R) (q : Rat) : val3 x (pack3 q) = algebraMap ℚ R q := by
  simp [val3,v3,pack3]
@[simp] theorem val9_pack (x y : R) (q : Rat) :
    val9 x y (pack9 q) = algebraMap ℚ R q := by simp [val9,v3,pack9]
@[simp] theorem val_pack (x y z : R) (q : Rat) :
    val x y z (pack q) = algebraMap ℚ R q := by simp [val,v2,pack]

theorem val3_add (x : R) (p q : C3) : val3 x (add3 p q) = val3 x p+val3 x q :=
  v3_a3 (map_add (algebraMap ℚ R)) x p q
theorem val9_add (x y : R) (p q : C9) : val9 x y (add9 p q) = val9 x y p+val9 x y q :=
  v3_a3 (val3_add x) y p q
theorem val_add (x y z : R) (p q : C18) : val x y z (add p q) = val x y z p+val x y z q :=
  v2_a2 (val9_add x y) z p q

theorem val3_mul {D : Reductions} {x : R} (h : x^3=val3 x D.inner) (p q : C3) :
    val3 x (mul3 D p q) = val3 x p*val3 x q :=
  v3_m3 (map_add (algebraMap ℚ R)) (map_mul (algebraMap ℚ R)) h p q
theorem val9_mul {D : Reductions} {x y : R} (hx : x^3=val3 x D.inner)
    (hy : y^3=val9 x y D.middle) (p q : C9) :
    val9 x y (mul9 D p q) = val9 x y p*val9 x y q :=
  v3_m3 (val3_add x) (val3_mul hx) hy p q

theorem val_mul {D : Reductions} {x y z : R} (h : Roots D x y z) (p q : C18) :
    val x y z (mul D p q)=val x y z p*val x y z q :=
  v2_m2 (val9_add x y) (val9_mul h.inner h.middle) h.outer p q

end RKResearch.Certified.CubicCubicQuadraticRatReplay

#print axioms RKResearch.Certified.CubicCubicQuadraticRatReplay.val_mul
