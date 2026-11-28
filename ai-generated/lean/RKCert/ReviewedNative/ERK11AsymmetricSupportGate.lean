/-! Denominator-cleared support row for a genuine dormant site. The actual
clock masks and signed Lagrange quadrature are established separately. -/
namespace RKResearch.ERK11AsymmetricSupportGate

open Lean.Grind
variable {R : Type} [CommRing R]

theorem supportLinear
    (p q z e t s delta sigma pi omega g : R)
    (hS : delta*(t+s)=sigma)
    (hP : delta*t*s=pi)
    (hW : delta*(z-e)*(z-t)*(p+q*s)=omega*g) :
    (z-e)*(p*z*delta+q*z*sigma-q*pi-(p+q*z)*(delta*t))
      -omega*g=0 := by
  rw [← hS, ← hP, ← hW]
  grind

/- In the application, f = z(1-z)(z-a)(z-d), u = (z-s)(z-h),
and v = (z-e)(z-t). Keeping them factored avoids expanding clock products. -/
theorem maskedVandermondeCancellation
    (I pool f u v : R) (hw : I*(f*u*v)=pool*u*f^2) :
    (f*u)*(I*v-pool*f)=0 := by
  have h' : (f*u)*(I*v-pool*f)=I*(f*u*v)-pool*u*f^2 := by grind
  rw [h',hw]
  grind

end RKResearch.ERK11AsymmetricSupportGate

#print axioms RKResearch.ERK11AsymmetricSupportGate.supportLinear
#print axioms RKResearch.ERK11AsymmetricSupportGate.maskedVandermondeCancellation
