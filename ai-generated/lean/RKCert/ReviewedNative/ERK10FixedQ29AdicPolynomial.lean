module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-! Integer polynomial and auditable Horner jets for the fixed-q 29-adic chart. -/
namespace RKResearch.Certified.ERK10FixedQ29Adic
open Polynomial

abbrev F := ZMod 29
instance prime29 : Fact (Nat.Prime 29) := ⟨by decide +kernel⟩

/-- Ascending coefficients, with Horner multiplication by the indeterminate. -/
noncomputable def intPolynomial {R : Type*} [CommRing R] : List ℤ → Polynomial R
  | [] => 0
  | z :: zs => C (z : R) + X * intPolynomial zs

def intJet {R : Type*} [CommRing R] (x : R) : List ℤ → R × R
  | [] => (0, 0)
  | z :: zs =>
    let v := intJet x zs
    ((z : R) + x * v.1, v.1 + x * v.2)

theorem eval_intPolynomial {R : Type*} [CommRing R] (zs : List ℤ) (x : R) :
    (intPolynomial zs).eval x = (intJet x zs).1 := by
  induction zs with
  | nil => simp [intPolynomial, intJet]
  | cons z zs ih => simp [intPolynomial, intJet, ih]

theorem eval_derivative_intPolynomial {R : Type*} [CommRing R] (zs : List ℤ) (x : R) :
    (intPolynomial zs).derivative.eval x = (intJet x zs).2 := by
  induction zs with
  | nil => simp [intPolynomial, intJet]
  | cons z zs ih =>
    simp [intPolynomial, intJet, derivative_add, derivative_mul, ih, eval_intPolynomial]

theorem map_intPolynomial {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (zs : List ℤ) : (intPolynomial zs).map f = intPolynomial zs := by
  induction zs with
  | nil => simp [intPolynomial]
  | cons z zs ih => simp [intPolynomial, ih]

def decicCoeffs : List ℤ :=
  [8840760201800, -253467892079060, 3137934176909504,
    -22147907712268517, 99189988063653812, -295624157281470449,
    595327896073372740, -801391965499578390, 691140376781707950,
    -345177595434956400, 75851682979590000]

noncomputable def decic (R : Type*) [CommRing R] : Polynomial R := intPolynomial decicCoeffs

theorem map_decic {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (decic R).map f = decic S := map_intPolynomial f _

theorem decic_residue : (decic F).eval 2 = 0 := by
  rw [decic, eval_intPolynomial]
  decide +kernel

theorem decic_derivative_residue : (decic F).derivative.eval 2 = 16 := by
  rw [decic, eval_derivative_intPolynomial]
  decide +kernel

theorem decic_leading_residue : (75851682979590000 : F) = 25 := by
  decide +kernel

end RKResearch.Certified.ERK10FixedQ29Adic
