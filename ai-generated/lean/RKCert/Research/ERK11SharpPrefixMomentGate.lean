import Lean

/-!
# Three independent rooted alias moments for the repaired dense family

This Lean-core file checks exact rational witnesses on the literal
first eight rows of the archived construction. Each witness is
a degree-five rooted profile minus a specified combination through
degree four. Applying one unary root makes it invisible on any
three appended rows fed only from those eight. The accompanying
argument transfers the certificate to paid fields and applies
the ordinary extension's positive-moment rank bound.
-/
namespace RKResearch.ERK11SharpPrefixMomentGate

abbrev VR := List Rat

def a8 : List VR :=
  [ [0,0,0,0,0,0,0,0],
    [1/4,0,0,0,0,0,0,0],
    [0,1/2,0,0,0,0,0,0],
    [1,-2,2,0,0,0,0,0],
    [1/6,0,4/6,1/6,0,0,0,0],
    [11/162,48/162,-4/162,-5/162,4/162,0,0,0],
    [19/162,0,-20/162,3/162,-2/162,54/162,0,0],
    [1400/12288,0,-1312/12288,212/12288,-144/12288,3645/12288,-729/12288,0] ]

def dot (p q : VR) : Rat := (p.zipWith (·*·) q).foldr (·+·) 0
def a (v : VR) : VR := a8.map (fun r => dot r v)
def one8 : VR := List.replicate 8 1
def clock : VR := a one8
def mon (k : Nat) : VR := clock.map (·^k)
def mul (v w : VR) : VR := v.zipWith (·*·) w
def add (v w : VR) : VR := v.zipWith (·+·) w

/-- The rooted inputs are 1, c, c², c³, c⁴, Ac, A²c, c⊙A²c. -/
def basisActual : List VR :=
  [one8,clock,mon 2,mon 3,mon 4,a clock,a (a clock),mul clock (a (a clock))]

/-- Model polynomial coefficients in ascending order, through degree five. -/
def basisModel : List VR :=
  [ [1,0,0,0,0,0], [0,1,0,0,0,0], [0,0,1,0,0,0], [0,0,0,1,0,0],
    [0,0,0,0,1,0], [0,0,1/2,0,0,0], [0,0,0,1/6,0,0], [0,0,0,0,1/6,0] ]

def comb (size : Nat) (coef : VR) (basis : List VR) : VR :=
  (coef.zipWith (fun t v => v.map (t*·)) basis).foldr add (List.replicate size 0)

def coefficient1 : VR := [0,-5/192,725/4608,-47/192,37/288,-23/768,-1/3,1/3]
def coefficient2 : VR := [0,-1/48,305/2304,-23/96,25/144,-11/384,-5/48,-1/48]
def coefficient3 : VR := [0,-1/24,5/12,-35/24,25/12,0,0,0]

/-- The numerical grade-five witnesses are A⁵1, A³(c²), and c⁵. -/
theorem actualWitnesses :
    comb 8 coefficient1 basisActual = a (a (a (a (a one8)))) ∧
    comb 8 coefficient2 basisActual = a (a (a (mon 2))) ∧
    comb 8 coefficient3 basisActual = mon 5 := by
  decide +kernel

def poly1 : VR := [0,0,0,0,0,1/120]
def poly2 : VR := [0,0,0,0,0,1/60]
def poly3 : VR := [0,0,0,0,0,1]
def gap (nominal coef : VR) : VR := nominal.zipWith (·-·) (comb 6 coef basisModel)
def p1 : VR := gap poly1 coefficient1
def p2 : VR := gap poly2 coefficient2
def p3 : VR := gap poly3 coefficient3

theorem models :
    p1 = [0,5/192,-41/288,173/576,-53/288,1/120] ∧
    p2 = [0,1/48,-17/144,37/144,-49/288,1/60] ∧
    p3 = [0,1/24,-5/12,35/24,-25/12,1] := by
  decide +kernel

def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1)*factorial n

def ell (m : Nat) (p : VR) : Rat :=
  dot p ((List.range 6).map (fun k =>
    ((factorial k * factorial m : Nat) : Rat) / (factorial (k+m+1) : Rat)))

def det3 (a b c d e f g h i : Rat) : Rat :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

/-- The three independent moment columns are for Jp₁,Jp₂,Jp₃
against ℓ₁,ℓ₂,ℓ₃. A single upper primitive shifts the weight once. -/
theorem paidMomentDet :
    det3 (ell 2 p1) (ell 2 p2) (ell 2 p3)
         (ell 3 p1) (ell 3 p2) (ell 3 p3)
         (ell 4 p1) (ell 4 p2) (ell 4 p3) =
       -(1 : Rat)/(2^17*3^7*5^4*7^3) := by
  decide +kernel

theorem matrixValues :
    ell 2 p1 = 11/15120 ∧ ell 2 p2 = 17/30240 ∧ ell 2 p3 = 0 ∧
    ell 3 p1 = 1/2304 ∧ ell 3 p2 = 3/8960 ∧ ell 3 p3 = 1/10080 ∧
    ell 4 p1 = 2173/7257600 ∧ ell 4 p2 = 419/1814400 ∧ ell 4 p3 = 1/8640 := by
  decide +kernel


def scale (q : Rat) (v : VR) : VR := v.map (q*·)
def H4Coeff : VR := [0,-1,8,-19,12,0]
def XH4Coeff : VR := [0,0,-1,8,-19,12]
def n1 : VR := scale 2880 p1
def n2 : VR := scale 1440 p2
def n3 : VR := scale 24 p3

/-- A compact basis of the same paid alias space for the coupled
continuation. H4 has roots 0, 1, 1/3, 1/4. -/
theorem alternateAliases :
    scale (1/10) (add (add (scale 5 n3) (scale 3 n1)) (scale (-8) n2)) = H4Coeff ∧
    scale (1/2) (add n3 H4Coeff) = XH4Coeff ∧
    n1 = [0,75,-410,865,-530,24] := by
  decide +kernel

end RKResearch.ERK11SharpPrefixMomentGate
#print axioms RKResearch.ERK11SharpPrefixMomentGate.actualWitnesses
#print axioms RKResearch.ERK11SharpPrefixMomentGate.models
#print axioms RKResearch.ERK11SharpPrefixMomentGate.paidMomentDet
#print axioms RKResearch.ERK11SharpPrefixMomentGate.matrixValues
#print axioms RKResearch.ERK11SharpPrefixMomentGate.alternateAliases
