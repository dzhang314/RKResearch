module

public import RKCert.ReviewedNative.DIRK12F17CubicCore
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace RKResearch.Certified.DIRK12F17Cubic

set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem reads_nodes : VecEq (A0 rawOne) rawC := by decide +kernel

theorem reads_ghosts :
    (∀ i, ghost i → rawB i = num 0) ∧
    (∀ k : Fin 3, ∀ i, ¬ ghost i → genF k.val i = num 0) ∧
    (∀ k : Fin 3, ∀ i, ghost i → genB k.val i = num 0) := by decide +kernel

theorem reads_fA (d : Nat) (hd : d < 5) (i : Fin (width d)) :
    VecEq (A0 (genF i.val)) (combo genF d 0 i.val) := by
  interval_cases d <;> (first | exact Fin.elim0 i | fin_cases i <;> decide +kernel)

theorem reads_fC (d : Nat) (hd : d < 5) (i : Fin (width d)) :
    VecEq (mulV rawC (genF i.val)) (combo genF d 1 i.val) := by
  interval_cases d <;> (first | exact Fin.elim0 i | fin_cases i <;> decide +kernel)

theorem reads_fP (d : Nat) (hd : d < 5) :
    VecEq (fprim d) (combo genF d 2 0) := by
  interval_cases d <;> decide +kernel

theorem reads_bA (d : Nat) (hd : d < 5) (i : Fin (width d)) :
    VecEq (N0 (genB i.val)) (combo genB d 3 i.val) := by
  interval_cases d <;> (first | exact Fin.elim0 i | fin_cases i <;> decide +kernel)

theorem reads_bY (d : Nat) (hd : d < 5) (i : Fin (width d)) :
    VecEq (mulV rawY (genB i.val)) (combo genB d 4 i.val) := by
  interval_cases d <;> (first | exact Fin.elim0 i | fin_cases i <;> decide +kernel)

theorem reads_bP (d : Nat) (hd : d < 5) :
    VecEq (bprim d) (combo genB d 5 0) := by
  interval_cases d <;> decide +kernel

theorem reads_bSilent (d : Nat) (hd : d ≤ 5) (j : Nat) (hj : d+j < 12)
    (i : Fin (width d)) : rdot (genB i.val) (powC j) = num 0 := by
  have hjBound : j < 12-d := by omega
  interval_cases d <;> (first | exact Fin.elim0 i |
    simp only [Nat.reduceSub] at hjBound; interval_cases j <;> fin_cases i <;> decide +kernel)

theorem reads_fASilent (k i : Fin 3) :
    rdot (genB i.val) (A0 (genF k.val)) = num 0 := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem reads_fAMoment (k : Fin 3) (j : Fin 6) :
    rdot (rW j.val) (A0 (genF k.val)) = num 0 := by
  fin_cases k <;> fin_cases j <;> decide +kernel

theorem reads_fPSilent (i : Fin 3) : rdot (genB i.val) (fprim 5) = num 0 := by
  fin_cases i <;> decide +kernel

theorem reads_fPMoment (j : Fin 6) : rdot (rW j.val) (fprim 5) = num 0 := by
  fin_cases j <;> decide +kernel

theorem reads_scalar (j : Nat) (hj : j < 12) :
    mul (num (j+1)) (rdot rawB (powC j)) = num 1 := by
  interval_cases j <;> decide +kernel

theorem reads_witness : nextDefect = ⟨11,7,12⟩ := by decide +kernel
theorem reads_nextUnit : mul nextDefect starInverse = num 1 := by decide +kernel
theorem reads_diagUnit : mul (rawA 1 1) diagInverse = num 1 := by decide +kernel
theorem reads_firstDiag : rawA 0 0 = num 0 := by decide +kernel

theorem receipts : Receipts where
  nodes := reads_nodes
  ghosts := reads_ghosts.1
  fSupport := reads_ghosts.2.1
  bSupport := reads_ghosts.2.2
  fA := reads_fA
  fC := reads_fC
  fP := reads_fP
  bA := reads_bA
  bY := reads_bY
  bP := reads_bP
  bSilent := reads_bSilent
  fASilent := reads_fASilent
  fAMoment := reads_fAMoment
  fPSilent := reads_fPSilent
  fPMoment := reads_fPMoment
  scalar := reads_scalar
  witness := reads_witness
  nextUnit := reads_nextUnit
  diagUnit := reads_diagUnit
  firstDiag := reads_firstDiag

end RKResearch.Certified.DIRK12F17Cubic
