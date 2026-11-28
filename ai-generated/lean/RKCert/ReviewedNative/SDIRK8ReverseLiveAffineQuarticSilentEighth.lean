module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ReverseLiveAffineQuarticSilentEighth

open scoped Matrix BigOperators

/-- A degree-drop-safe padded Sylvester matrix for the prospective fifth
quadratic and the six-peg cubic. -/
def literalFifthSylvester {R : Type*} [CommRing R]
    (a b c d e f h : R) : Matrix (Fin 5) (Fin 5) R :=
  !![c,b,a,0,0;
     0,c,b,a,0;
     0,0,c,b,a;
     h,f,e,d,0;
     0,h,f,e,d]

/-- Their shared actual root gives a kernel vector with one unit coordinate.
No leading coefficient is assumed nonzero at the prospective tableau. -/
theorem literalFifthResultantZero {R : Type*} [CommRing R]
    (a b c d e f h y : R) (h₂ : a*y^2+b*y+c=0) (h₃ : d*y^3+e*y^2+f*y+h=0) :
    (literalFifthSylvester a b c d e f h).det=0 := by
  let v : Fin 5 → R := ![1,y,y^2,y^3,y^4]
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors (v := v) (i := 0)
  · funext i
    change (∑ j, literalFifthSylvester a b c d e f h i j * v j) = 0
    refine Fin.cases ?_ (fun i₁ => Fin.cases ?_ (fun i₂ => Fin.cases ?_
      (fun i₃ => Fin.cases ?_ (fun i₄ => Fin.cases ?_ (fun z => Fin.elim0 z) i₄) i₃)
      i₂) i₁) i
    all_goals simp [literalFifthSylvester,v,Fin.sum_univ_succ]
    · linear_combination h₂
    · linear_combination y*h₂
    · linear_combination y^2*h₂
    · linear_combination h₃
    · linear_combination y*h₃
  · simp [v]

/-- At an exceptional diagonal where the padded fourth equation has a
literal root, actual distinctness forces the other linear factor to vanish. -/
theorem alternateFourth {R : Type*} [CommRing R] [NoZeroDivisors R]
    (j₀ j₁ j₂ a s : R) (hne : s≠a)
    (hpadded : j₀+j₁*a+j₂*a^2=0) (hactual : j₀+j₁*s+j₂*s^2=0) :
    j₂*s= -j₁-j₂*a := by
  have hz : (s-a)*(j₂*s-(-j₁-j₂*a))=0 := by
    linear_combination hactual-hpadded
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne))

/-- Terminal normalization of an affine reverse barycentric numerator,
stated without inverting a weight or a formal leading coefficient. -/
theorem affineReverseFromTerminal {R : Type*} [CommRing R]
    (di dx wi wx qi qx k : R)
    (hi : di*wi=k*qi) (hx : dx*wx=k*qx) :
    qx*di*wi=qi*dx*wx := by
  linear_combination qx*hi-qi*hx

#print axioms literalFifthResultantZero
#print axioms alternateFourth
#print axioms affineReverseFromTerminal

end RKCert.ReviewedNative.SDIRK8ReverseLiveAffineQuarticSilentEighth
