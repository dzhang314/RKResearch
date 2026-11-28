import Init

namespace RKResearch.Certified.DIRK10CubicReverseLeadingArithmetic

def terms : List Int := [0,1,-14,56,-84,42]

def clearedMoments : List Int :=
  (List.range 5).map fun j =>
    ((List.range 6).map fun k =>
      terms[k]?.getD 0 * Int.ofNat (2520/(k+j+1))).foldl (· + ·) 0

theorem jacobi_moments : clearedMoments = [84,84,84,84,84] := by decide

def q6 (x : Int) : Int :=
  x*(1296-14*216*x+56*36*x*x-84*6*x*x*x+42*x*x*x*x)

def scaledGate (u p : Int) : Int :=
  u*u*u*(2*p-u)*q6 p - p*p*p*(2*u-p)*q6 u

def options : List Int := [-1,1,2,3,4,5]

def gates : List Int :=
  options.flatMap fun u => (options.filter (· != u)).map (scaledGate u)

theorem causal_gates : gates.length = 30 ∧ gates.all (· != 0) = true := by decide

#print axioms jacobi_moments
#print axioms causal_gates

end RKResearch.Certified.DIRK10CubicReverseLeadingArithmetic
