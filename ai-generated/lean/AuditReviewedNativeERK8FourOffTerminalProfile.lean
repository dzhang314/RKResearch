import RKCert.ReviewedNative.ERK8FourOffTerminalProfile

open Polynomial RKResearch RKResearch.Certified.Graded
open RKResearch.Certified.Graded.OneOff RKResearch.Certified.Graded.ERKTaggedHorizon
open RKResearch.Certified.Graded.FourOffNewton RKCert.Endpoint
open scoped Matrix Classical

section

variable {K : Type*} [Field K] [CharZero K]

example (A : Matrix (Fin 10) (Fin 10) K) (b : Fin 10 → K)
    (order : RKResearch.HasOrder 8 A b) (bandFour : zeroSpace A 4=band A 2)
    (paidTerminal : Reverse.coordinate (K:=K) (9:Fin 10)∈treeSpace A 4)
    (terminalClean : g A (Fin.last 9)=0) (terminalClock : nodes A (Fin.last 9)=1)
    (cleanFive : (cleanKnots A).card=5) :
    ∃ R : K[X], R.natDegree≤2 ∧
      (nodalHull ((cleanKnots A).erase 1)).eval 1≠0 ∧
      evalNodes A (nodalHull ((cleanKnots A).erase 1))+diag (g A) (evalNodes A R)=
        (nodalHull ((cleanKnots A).erase 1)).eval 1 • (Pi.single (Fin.last 9) (1:K) : Fin 10 → K) :=
  terminal_profile_of_unitNine order bandFour paidTerminal terminalClean terminalClock cleanFive

end

#print axioms RKResearch.Certified.Graded.FourOffNewton.terminal_profile_of_unitNine
