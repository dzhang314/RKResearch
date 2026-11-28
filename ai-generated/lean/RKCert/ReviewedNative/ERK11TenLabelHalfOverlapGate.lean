/-! Division-free scalar certificates for the ten-label half-overlap chart. -/
namespace RKResearch.ERK11TenLabelHalfOverlapGate
open Lean.Grind
variable {R : Type} [CommRing R]

def jacobi4 (x : R) : R := 42*x^4-84*x^3+56*x^2-14*x+1
def jacobi5 (x : R) : R := 132*x^5-330*x^4+300*x^3-120*x^2+20*x-1
def jacobi4D (x : R) : R := 168*x^3-252*x^2+112*x-14
def jacobi5D (x : R) : R := 660*x^4-1320*x^3+900*x^2-240*x+20

def valueMinor (x : R) : R :=
  2772*x^8-22176*x^7+74088*x^6-134064*x^5+142332*x^4
    -89520*x^3+31864*x^2-5648*x+353
def derivMinor (x : R) : R :=
  1386*x^8-11088*x^7+41202*x^6-85050*x^5+102015*x^4
    -70968*x^3+27269*x^2-5086*x+325

def bezoutValue (x : R) : R :=
  16195538392 - 231428849627*x + 1051816146834*x^2
    - 2164681755495*x^3 + 2294810833140*x^4 - 1306784001159*x^5
    + 393390636408*x^6 - 54796857192*x^7
def bezoutDeriv (x : R) : R :=
  -17590600202 + 257541514243*x - 1245912798462*x^2
    + 2833482948828*x^3 - 3434808706056*x^4 + 2284786859166*x^5
    - 786781272816*x^6 + 109593714384*x^7

theorem specializedValues (x : R) :
    jacobi4 x * jacobi5 (x-1) - jacobi5 x * jacobi4 (x-1) =
      -2 * valueMinor x := by
  unfold jacobi4 jacobi5 valueMinor
  grind

theorem specializedDerivatives (x : R) :
    jacobi4 x * (jacobi5D x + jacobi5D (x-1)) -
      jacobi5 x * (jacobi4D x + jacobi4D (x-1)) =
      8 * derivMinor x := by
  unfold jacobi4 jacobi5 jacobi4D jacobi5D derivMinor
  grind

theorem halfOverlapBezout (x : R) :
    bezoutValue x * valueMinor x + bezoutDeriv x * derivMinor x = 79986726 := by
  unfold bezoutValue valueMinor bezoutDeriv derivMinor
  grind

end RKResearch.ERK11TenLabelHalfOverlapGate
#print axioms RKResearch.ERK11TenLabelHalfOverlapGate.specializedValues
#print axioms RKResearch.ERK11TenLabelHalfOverlapGate.specializedDerivatives
#print axioms RKResearch.ERK11TenLabelHalfOverlapGate.halfOverlapBezout
