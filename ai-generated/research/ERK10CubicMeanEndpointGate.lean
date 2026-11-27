import Lean

/-! Exact scalar endpoint exit for the remaining cubic ERK10 weighted mean. -/
namespace RKResearch.ERK10CubicMeanEndpointGate
open Lean.Grind
variable {K : Type} [Field K]

def L (p : K) : K := 42*p^4-84*p^3+56*p^2-14*p+1
def N (p : K) : K := 1260*p^5-2940*p^4+2580*p^3-1055*p^2+195*p-12
def R (p : K) : K := 60*p^3-75*p^2+25*p-2

theorem normRemainder (p : K) : N p-R p=(30*p-10)*L p := by
  unfold N R L
  grind

theorem normOne (p : K) :
    (-16800*p^2+18900*p-4675)*L p-
    (-11760*p^3+22050*p^2-12950*p+2338)*R p=1 := by
  unfold L R
  grind

def term (a : List Int) (n : Nat) : Int := (a[n]?).getD 0
def prod (a b : List Int) : List Int :=
  (List.range (a.length+b.length-1)).map (fun k =>
    (List.range (k+1)).foldl (fun s i => s+term a i*term b (k-i)) 0)

def integrated (p : Int) : Int :=
  let left := [0,0,0,10*p^2,-15*p,6]
  let Lquot := [42*p^3-84*p^2+56*p-14,42*p^2-84*p+56,42*p-84,42]
  let all := prod left (prod [-1,1] Lquot)
  all.zipIdx.foldl (fun s (a,i) => s+a*(2520/(i+1):Int)) 0

def intN (p : Int) : Int := 1260*p^5-2940*p^4+2580*p^3-1055*p^2+195*p-12

theorem integralGrid : ∀ p : Fin 6, integrated (Int.ofNat p.val) =
    -42*intN (Int.ofNat p.val) := by decide

end RKResearch.ERK10CubicMeanEndpointGate
#print axioms RKResearch.ERK10CubicMeanEndpointGate.normRemainder
#print axioms RKResearch.ERK10CubicMeanEndpointGate.normOne
#print axioms RKResearch.ERK10CubicMeanEndpointGate.integralGrid
