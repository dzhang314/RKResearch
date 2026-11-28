import Lean

/-! Arithmetic for the opposite-corner inverse Gram gate. -/
namespace RKResearch.ERK11MiddleInverseGate

def W (i j : Fin 5) : Int :=
  #[#[4620, 2310, 1386, 924, 660],
    #[2310, 924, 462, 264, 165],
    #[1386, 462, 198, 99, 55],
    #[924, 264, 99, 44, 22],
    #[660, 165, 55, 22, 10]][i.val]![j.val]!

def N (i j : Fin 5) : Int :=
  #[#[1, -16, 72, -120, 66],
    #[-16, 248, -1080, 1740, -924],
    #[72, -1080, 4560, -7140, 3696],
    #[-120, 1740, -7140, 10920, -5544],
    #[66, -924, 3696, -5544, 2772]][i.val]![j.val]!

def sum5 (f : Fin 5 → Int) : Int := f 0 + f 1 + f 2 + f 3 + f 4

theorem gramInverse : ∀ i j : Fin 5,
    sum5 (fun k => W i k * N k j) = (if i = j then 132 else 0) := by decide

open Lean.Grind
variable {K : Type} [Field K]

def polyP (x : K) : K := 330*x^4-480*x^3+216*x^2-32*x+1
def polyD (y : K) : K := 35*(1980*y^4-1344*y^3+324*y^2-32*y+1)

def mixed (x y a b : K) : K :=
    (1+b)*((1+a)-32*x+216*x^2-480*x^3+330*x^4)
    + (2*y)*(-16*(1+a)+496*x-3240*x^2+6960*x^3-4620*x^4)
    + (3*y^2)*(72*(1+a)-2160*x+13680*x^2-28560*x^3+18480*x^4)
    + (4*y^3)*(-120*(1+a)+3480*x-21420*x^2+43680*x^3-27720*x^4)
    + (5*y^4)*(66*(1+a)-1848*x+11088*x^2-22176*x^3+13860*x^4)

set_option maxHeartbeats 3000000 in
theorem reduceMixed (x a b : K) :
    mixed x (1-x) a b =
      a*b + polyP (1-x)*a + polyP x*b + polyD (x*(1-x)) := by
  unfold mixed polyP polyD
  grind

theorem halfClock (x a b : K) (hx : 2*x = 1) :
    64 * mixed x (1-x) a b = 64*a*b-24*a-24*b-35 := by
  rw [reduceMixed]
  unfold polyP polyD
  grind

end RKResearch.ERK11MiddleInverseGate
#print axioms RKResearch.ERK11MiddleInverseGate.gramInverse
#print axioms RKResearch.ERK11MiddleInverseGate.reduceMixed
#print axioms RKResearch.ERK11MiddleInverseGate.halfClock
