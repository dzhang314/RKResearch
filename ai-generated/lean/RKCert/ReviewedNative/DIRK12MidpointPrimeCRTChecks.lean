module

public import RKCert.ReviewedNative.DIRK12MidpointPrimeCRTData
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace RKResearch.Certified.DIRK12MidpointPrimeCRT

open DualSupport12VectorReplay

set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem reads_nodes : EqV (A0 packet 1) packet.c := by decide +kernel

theorem reads_ghosts :
    (∀ i, ghost i → packet.b i = 0) ∧
    (∀ k : Fin 3, ∀ i, ¬ ghost i → packet.genF k.val i = 0) ∧
    (∀ k : Fin 3, ∀ i, ghost i → packet.genB k.val i = 0) := by decide +kernel

theorem reads_fA (d : Nat) (hd : d < 5) (i : Fin (width d)) :
    EqV (A0 packet (packet.genF i.val)) (combo packet packet.genF d 0 i.val) := by
  interval_cases d <;> (first | exact Fin.elim0 i | fin_cases i <;> decide +kernel)

theorem reads_fC (d : Nat) (hd : d < 5) (i : Fin (width d)) :
    EqV (packet.c * packet.genF i.val) (combo packet packet.genF d 1 i.val) := by
  interval_cases d <;> (first | exact Fin.elim0 i | fin_cases i <;> decide +kernel)

theorem reads_fP (d : Nat) (hd : d < 5) :
    EqV (F packet d) (combo packet packet.genF d 2 0) := by
  interval_cases d <;> decide +kernel

theorem reads_bA (d : Nat) (hd : d < 5) (i : Fin (width d)) :
    EqV (N0 packet (packet.genB i.val)) (combo packet packet.genB d 3 i.val) := by
  interval_cases d <;> (first | exact Fin.elim0 i | fin_cases i <;> decide +kernel)

theorem reads_bY (d : Nat) (hd : d < 5) (i : Fin (width d)) :
    EqV (Y packet * packet.genB i.val) (combo packet packet.genB d 4 i.val) := by
  interval_cases d <;> (first | exact Fin.elim0 i | fin_cases i <;> decide +kernel)

theorem reads_bP (d : Nat) (hd : d < 5) :
    EqV (B packet d) (combo packet packet.genB d 5 0) := by
  interval_cases d <;> decide +kernel

theorem reads_bSilent (d : Nat) (hd : d ≤ 5) (j : Nat) (hj : d+j < 12)
    (i : Fin (width d)) : pair (packet.genB i.val) (packet.c^j) = 0 := by
  have hjBound : j < 12-d := by omega
  interval_cases d <;> (first | exact Fin.elim0 i |
    simp only [Nat.reduceSub] at hjBound; interval_cases j <;> fin_cases i <;> decide +kernel)

theorem reads_fASilent (k i : Fin 3) :
    pair (packet.genB i.val) (A0 packet (packet.genF k.val)) = 0 := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem reads_fAMoment (k : Fin 3) (j : Fin 6) :
    pair (W packet j.val) (A0 packet (packet.genF k.val)) = 0 := by
  fin_cases k <;> fin_cases j <;> decide +kernel

theorem reads_fPSilent (i : Fin 3) : pair (packet.genB i.val) (F packet 5) = 0 := by
  fin_cases i <;> decide +kernel

theorem reads_fPMoment (j : Fin 6) : pair (W packet j.val) (F packet 5) = 0 := by
  fin_cases j <;> decide +kernel

theorem reads_scalar (j : Nat) (hj : j < 12) :
    ((j+1 : Nat) : K) * pair packet.b (packet.c^j) = 1 := by
  interval_cases j <;> decide +kernel

theorem reads_witness : nextDefect packet = (starNum : K) := by decide +kernel
theorem reads_nextUnit : nextDefect packet * packet.starInverse = 1 := by decide +kernel
theorem reads_diagUnit : matrix packet 1 1 * packet.diagInverse = 1 := by decide +kernel
theorem reads_firstDiag : matrix packet 0 0 = 0 := by decide +kernel

theorem reads_small (j : Fin 5) : ((j.val+1 : Nat) : K) * (smallInv[j.val]! : K) = 1 := by
  fin_cases j <;> decide +kernel

theorem units (j : Nat) (hj : j < 5) : IsUnit (((j+1 : Nat) : K)) :=
  IsUnit.of_mul_eq_one (smallInv[j]! : K) (reads_small ⟨j,hj⟩)

theorem receipts : Receipts packet where
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
  nextUnit := reads_nextUnit
  diagUnit := reads_diagUnit
  firstDiag := reads_firstDiag

end RKResearch.Certified.DIRK12MidpointPrimeCRT
