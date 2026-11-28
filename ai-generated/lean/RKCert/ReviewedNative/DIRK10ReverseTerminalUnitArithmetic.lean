import Init

namespace RKResearch.Certified.DIRK10ReverseTerminalUnitArithmetic

def hilbert52 : List (List Int) :=
  (List.range 5).map fun i => (List.range 5).map fun j =>
    Int.ofNat (2520 / (i+j+1))

def invHilbert52 : List (List Int) :=
  [[25,-300,1050,-1400,630],
   [-300,4800,-18900,26880,-12600],
   [1050,-18900,79380,-117600,56700],
   [-1400,26880,-117600,179200,-88200],
   [630,-12600,56700,-88200,44100]]

def getMatrix (M : List (List Int)) (i j : Nat) : Int :=
  (M[i]?.getD [])[j]?.getD 0

def mulMatrix (M N : List (List Int)) : List (List Int) :=
  (List.range 5).map fun i => (List.range 5).map fun j =>
    (((List.range 5).map fun k => getMatrix M i k * getMatrix N k j).foldl (· + ·) 0)

def id2520 : List (List Int) :=
  (List.range 5).map fun i => (List.range 5).map fun j => if i == j then 2520 else 0

theorem hilbert_integer_inverse :
    mulMatrix hilbert52 invHilbert52 = id2520 ∧
    mulMatrix invHilbert52 hilbert52 = id2520 := by decide

def legendreFive : List Int := [-1,30,-210,560,-630,252]

def clearedIntegrals : List Int :=
  (List.range 5).map fun i =>
    (((List.range 6).map fun k =>
       legendreFive[k]?.getD 0 * Int.ofNat (2520 / (i+k+1))).foldl (· + ·) 0)

theorem legendre_scalar_receipts :
    clearedIntegrals = [0,0,0,0,0] ∧
    legendreFive.getLastD 0 = 252 ∧ legendreFive.headD 0 = -1 ∧
    (3628800 : Nat) % 2520 = 0 ∧ (2520 : Nat) % 252 = 0 := by decide

#print axioms hilbert_integer_inverse
#print axioms legendre_scalar_receipts

end RKResearch.Certified.DIRK10ReverseTerminalUnitArithmetic
