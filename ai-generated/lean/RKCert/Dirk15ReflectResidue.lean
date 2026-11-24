module

public import RKCert.Dirk15SampleLift

@[expose] public section

/-! # Exact sign reversal of the parameter at the fixed good prime -/
namespace RKCert.FixedPolynomial
open Polynomial RKCert.GoodPrimeDense
local notation "F" => ZMod 1009

def alternateResidue : Bool → List ℕ → List ℕ
  | _, [] => []
  | s, a::c => (if s then a else intResidue 1009 (-(a:ℤ)))::alternateResidue (!s) c

private theorem residuePoly_cons (a : ℕ) (l : List ℕ) :
    residuePoly (a::l)=C (a:F)+X*residuePoly l := by
  exact ofCoeffList_cons _ _

private theorem negative_residue_exact (a : ℕ) :
    (intResidue 1009 (-(a:ℤ)):F)=-(a:F) := by
  simpa only [Int.cast_neg,Int.cast_natCast] using
    (intResidue_cast (R:=F) (show 1009≠0 by decide) (-(a:ℤ)))

theorem alternateResidue_exact (c : List ℕ) (s : Bool) :
    residuePoly (alternateResidue s c)=
      if s then (residuePoly c).comp (-X) else -(residuePoly c).comp (-X) := by
  induction c generalizing s with
  | nil => cases s <;> simp [alternateResidue,residuePoly,RKCert.CompactResidue.polynomial,decode]
  | cons a c ih =>
    rw [alternateResidue,residuePoly_cons,residuePoly_cons,add_comp,mul_comp,C_comp,X_comp,ih]
    cases s <;> simp [negative_residue_exact,add_comm]

theorem minusParameter_reduction {P : ℤ[X]} {c : List ℕ}
    (h : P.map order15Reduce=residuePoly c) :
    (minusParameter P).map order15Reduce=residuePoly (alternateResidue true c) := by
  rw [minusParameter,Polynomial.map_comp,Polynomial.map_neg,Polynomial.map_X,h]
  exact (alternateResidue_exact c true).symm

end RKCert.FixedPolynomial
