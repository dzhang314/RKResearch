module
public import RKCert.DirkQuinticIntegerLists
public import RKCert.SplitFactorGate
@[expose] public section
namespace RKCert.Sextic
open RKCert.FixedFactor RKCert.DirkQuintic

/-- Evaluate the three cleared rows via Horner in an arbitrary commutative
ring. Coefficients of the unknown tableau do not occur in this test. -/
def quick {R:Type*} [CommRing R] (a b c d e f u:R):R :=
  let m₁:=1260*a+u*(840*b+u*(630*c+u*(504*d+u*(420*e+u*(360*f)))))
  let m₂:=840*a+u*(630*b+u*(504*c+u*(420*d+u*(360*e+u*(315*f)))))
  let m₃:=630*a+u*(504*b+u*(420*c+u*(360*d+u*(315*e+u*(280*f)))))
  m₁*m₃-m₂^2

def checkQuint (l:List ℤ):Bool :=
  let c:=coeffs l
  let a:=c 0;let b:=c 1;let q:=c 2;let d:=c 3;let e:=c 4;let f:=c 5
  integers10.all fun u=>decide (u∈l) || decide ((quick a b q d e f u)%15727≠0)

/-- Exactly 462 unordered five-element subsets (not arbitrary root permutations).
The eleven pivot candidates are checked, except when equal to an omitted root. -/
def pack (i:ℕ) : List (List ℤ) := ((integers10.sublistsLen 5).drop (i*11)).take 11

end RKCert.Sextic
