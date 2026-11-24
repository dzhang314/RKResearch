module
public import RKCert.DirkQuinticFixed10
@[expose] public section
namespace RKCert.PaidFifth
open RKCert.FixedFactor RKCert.DirkQuintic Polynomial RKCert.Paired.Terminal
/-- The 3+2 two-port determinant with one omitted grid knot, after removing
only its known powers of the physical nonzero/distinct pivots. -/
def minor {R:Type*} [CommRing R] (u v z:R):R:=
  735*v^4*z^3 - 1260*u^1*v^4*z^2 + 630*u^2*v^4*z^1 - 84*u^3*v^4 - 1960*v^3*z^4 + 2450*u^1*v^3*z^3 - 700*u^3*v^3*z^1 + 140*u^4*v^3 + 1260*v^2*z^5 + 672*u^1*v^2*z^4 - 3885*u^2*v^2*z^3 + 2220*u^3*v^2*z^2 - 120*u^4*v^2*z^1 - 60*u^5*v^2 - 2016*u^1*v^1*z^5 + 2688*u^2*v^1*z^4 - 960*u^4*v^1*z^2 + 240*u^5*v^1*z^1 + 840*u^2*z^5 - 1680*u^3*z^4 + 1050*u^4*z^3 - 200*u^5*z^2
noncomputable def test:MvPolynomial (Fin 3) ℤ := minor (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)
theorem eval_test {R:Type*} [CommRing R] (w:Fin 3→R):zEval test w=minor (w 0) (w 1) (w 2):=by
  simp [zEval,test,minor]
theorem homogeneous {R:Type*} [CommRing R] (a u v z:R):minor (a*u) (a*v) (a*z)=a^7*minor u v z:=by
  unfold minor;ring
def good (u:ZMod 15727):Bool:=grid10.all fun v=>grid10.all fun z=>
  decide (u=v ∨ u=z ∨ v=z ∨ minor u v z≠0)
end RKCert.PaidFifth

