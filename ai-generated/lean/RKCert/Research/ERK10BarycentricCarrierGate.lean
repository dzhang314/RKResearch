import Lean

/-! Scalar receipts for the positive-cardinality pooled tail cases. -/
namespace RKResearch.ERK10BarycentricCarrierGate
open Lean.Grind
variable {K : Type} [Field K]

private theorem nzMul {a b : K} (na : a ≠ 0) (nb : b ≠ 0) : a*b ≠ 0 :=
  fun z => nb ((Field.of_mul_eq_zero z).resolve_left na)

theorem varianceIdentity (a b x y : K) :
    (a+b)*(a*x^2+b*y^2)-(a*x+b*y)^2=a*b*(x-y)^2 := by grind

theorem uniqueRepeatedAmplitude (a b x y mean : K)
    (na : a ≠ 0) (nb : b ≠ 0)
    (first : a*x+b*y=(a+b)*mean)
    (second : a*x^2+b*y^2=(a+b)*mean^2) : x=y := by
  have eq := varianceIdentity a b x y
  rw [first,second] at eq
  have hz : (a*b)*((x-y)*(x-y))=0 := by grind
  rcases Field.of_mul_eq_zero ((Field.of_mul_eq_zero hz).resolve_left (nzMul na nb)) with h | h
  · grind
  · grind

theorem onePoleSquare (a b : K) (na : a ≠ 0) (h : a*b^2=0) : b=0 := by
  have hz := (Field.of_mul_eq_zero h).resolve_left na
  have hm : b*b=0 := by grind
  exact (Field.of_mul_eq_zero hm).elim id id

theorem twoPointProduct (b c x y : K) (h : b*x+c*y=0) :
    b*x^2+c*y^2= -(b+c)*x*y := by grind

theorem twoPointCubicCharge (b c x y : K) (h : b*x+c*y=0) :
    b*x^3+c*y^3=(x+y)*(b*x^2+c*y^2) := by grind

end RKResearch.ERK10BarycentricCarrierGate
#print axioms RKResearch.ERK10BarycentricCarrierGate.varianceIdentity
#print axioms RKResearch.ERK10BarycentricCarrierGate.uniqueRepeatedAmplitude
#print axioms RKResearch.ERK10BarycentricCarrierGate.onePoleSquare
#print axioms RKResearch.ERK10BarycentricCarrierGate.twoPointProduct
#print axioms RKResearch.ERK10BarycentricCarrierGate.twoPointCubicCharge
