import Lean

/-! The denominator-cleared common-clock entrance scaling and triplet exit. -/
namespace RKResearch.ERK10DoubledEntranceGate
open Lean.Grind
variable {K : Type} [Field K]

private theorem mulNZ {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a*b ≠ 0 :=
  fun h => hb ((Field.of_mul_eq_zero h).resolve_left ha)

theorem universalDoubling (t p a dr db r : K)
    (n4 : (4:K)≠0) (np : p≠0) (na : a≠0) (npt : p-t≠0)
    (q : dr+t*db+p*a=0)
    (c : 2*t*dr+3*t^2*db+3*p^2*a=0)
    (rr : 2*t*r=p^2*(3*t-2*p))
    (ar : (3*t-2*p)*(t^2*db+2*r*a)=2*t*(p-t)*dr) :
    p=2*t := by
  have h₁ : t^2*db=p*(2*t-3*p)*a := by grind
  have h₂ : t*dr=3*p*(p-t)*a := by
    have h := congrArg (fun v : K => t*v) q
    grind
  have h₃ := congrArg (fun v : K => t*v) ar
  have h₄ := congrArg (fun v : K => a*v) rr
  have h₅ := congrArg (fun v : K => t*v) h₁
  have h₆ := congrArg (fun v : K => 2*t*(p-t)*v) h₂
  have h : (4*(p*p)*a*(p-t))*(p-2*t)=0 := by grind
  have nz := mulNZ (mulNZ (mulNZ n4 (mulNZ np np)) na) npt
  have hp := (Field.of_mul_eq_zero h).resolve_left nz
  grind

def L (x : K) : K := 42*x^4-84*x^3+56*x^2-14*x+1

theorem lobattoUnitGap (x : K) :
    (-147*x^3+735*x^2-1222*x+677)*L x+
     (147*x^3-147*x^2+46*x-3)*L (x-1)=86 := by
  unfold L
  grind

end RKResearch.ERK10DoubledEntranceGate
#print axioms RKResearch.ERK10DoubledEntranceGate.universalDoubling
#print axioms RKResearch.ERK10DoubledEntranceGate.lobattoUnitGap
