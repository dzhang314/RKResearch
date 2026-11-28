module

public import RKCert.ReviewedNative.FiniteScaledOrderCheck
public import Mathlib.Algebra.Field.Rat

import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

namespace RKResearch.Certified.ERK10DirtySixthRelay

open RKResearch FiniteRootedTree
open scoped Matrix FiniteRootedTree

def AInt : Matrix (Fin 9) (Fin 9) ℤ :=
  !![0,0,0,0,0,0,0,0,0;
     122472,0,0,0,0,0,0,0,0;
     0,244944,0,0,0,0,0,0,0;
     91854,0,275562,0,0,0,0,0,0;
     918540,0,-3444525,3444525,0,0,0,0,0;
     -4059720,0,17350200,-13759200,1693440,0,0,0,0;
     113400,0,0,540000,483840,87480,0,0,0;
     143640,0,0,300000,-53760,18360,0,0,0;
     124320,0,0,160000,143360,25920,-45360,408240,0]

def PInt : Matrix (Fin 5) (Fin 9) ℤ :=
  !![756,0,0,0,0,0,0,0,0;
     -5628,0,0,20000,17920,3240,-4914,-10206,-20412;
     14889,0,0,-110000,-98560,-17820,27783,76545,107163;
     -16632,0,0,180000,161280,29160,-47628,-142884,-163296;
     6615,0,0,-90000,-80640,-14580,25515,76545,76545]

def normalizeA (d : ℤ) : Matrix (Fin 9) (Fin 9) ℚ :=
  Matrix.of fun i j => (AInt i j : ℚ)/d

def normalizeB (i : Fin 9) (d : ℤ) : Fin 9 → ℚ :=
  fun j => (AInt i j : ℚ)/d

def A : Matrix (Fin 9) (Fin 9) ℚ := normalizeA 1224720
def P : Matrix (Fin 5) (Fin 9) ℚ :=
  Matrix.of fun i j => (PInt i j : ℚ)/756

private theorem normalized_order (i : Fin 9) (d : ℤ) (p : ℕ)
    (hd : (d : ℚ) ≠ 0)
    (h : checkScaledOrder (fun v => AInt *ᵥ v) (fun v => AInt i ⬝ᵥ v) d d p = true) :
    HasOrder p (normalizeA d) (normalizeB i d) := by
  refine hasOrder_of_scaled_check (A := AInt) (b := AInt i) (d := d) (e := d) (p := p)
    (Int.castRingHom ℚ) (fun _ => rfl) (fun _ => rfl) ?_ ?_
    (isUnit_iff_ne_zero.mpr hd) (isUnit_iff_ne_zero.mpr hd) h
  · funext i j
    change (AInt i j : ℚ) = (d : ℚ) * ((AInt i j : ℚ) / d)
    exact (mul_div_cancel₀ (AInt i j : ℚ) hd).symm
  · funext j
    change (AInt i j : ℚ) = (d : ℚ) * ((AInt i j : ℚ) / d)
    exact (mul_div_cancel₀ (AInt i j : ℚ) hd).symm

set_option maxHeartbeats 6000000 in
theorem fsalPrimitive : HasOrder 5 (normalizeA 1224720) (normalizeB 6 1224720) :=
  normalized_order 6 1224720 5 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 6000000 in
theorem ghostPrimitive : HasOrder 4 (normalizeA 408240) (normalizeB 7 408240) :=
  normalized_order 7 408240 4 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 6000000 in
theorem relayPrimitive : HasOrder 5 (normalizeA 816480) (normalizeB 8 816480) :=
  normalized_order 8 816480 5 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 6000000 in
theorem ghostFifthBush :
    normalizeB 7 408240 ⬝ᵥ Φ (bushyTree 5) (normalizeA 408240) = (3/4 : ℚ) := by
  decide +kernel

theorem ghostNotFifth : ¬ HasOrder 5 (normalizeA 408240) (normalizeB 7 408240) := by
  intro h
  have hb := h (bushyTree 5) (by decide +kernel)
  rw [ghostFifthBush] at hb
  exact (by decide +kernel : ((bushyTree 5).factorial : ℚ) * (3/4 : ℚ) ≠ 1) hb

def decoderCheck : Bool :=
  (List.range 5).all fun n => (treesOfOrderSucc n).all fun t =>
    (List.finRange 5).all fun j =>
      decide ((t.forestFactorial : ℤ) * (PInt j ⬝ᵥ replayStage (fun v => AInt *ᵥ v) t) =
        if j.val = n then 756 * (1224720 : ℤ)^n else 0)

set_option maxHeartbeats 6000000 in
theorem exactDecoderNumerators : decoderCheck = true := by decide +kernel

end RKResearch.Certified.ERK10DirtySixthRelay

#print axioms RKResearch.Certified.ERK10DirtySixthRelay.fsalPrimitive
#print axioms RKResearch.Certified.ERK10DirtySixthRelay.ghostPrimitive
#print axioms RKResearch.Certified.ERK10DirtySixthRelay.relayPrimitive
#print axioms RKResearch.Certified.ERK10DirtySixthRelay.ghostNotFifth
#print axioms RKResearch.Certified.ERK10DirtySixthRelay.exactDecoderNumerators
