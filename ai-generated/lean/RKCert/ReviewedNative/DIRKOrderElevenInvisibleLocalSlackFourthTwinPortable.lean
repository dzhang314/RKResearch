import Lean

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSlackFourthTwinPortable

-- Coefficients are ascending elements of the residue ring, encoded as Nat.
def atC (p : List Nat) (i : Nat) : Nat := p[i]?.getD 0

def mulC (p q : List Nat) (i : Nat) : Nat :=
  ((List.range (i+1)).map (fun j => atC p j * atC q (i-j))).sum

def ok (a b c d : List Nat) (cap : Nat) : Bool :=
  (List.range (cap+1)).all (fun i =>
    (mulC a b i + mulC c d i) % 101 == (if i == 0 then 1 else 0))

def ordinary : List Nat := [45, 8, 48, 80, 69, 5, 10, 20, 23]

-- The two Q gcds in project.py are the primary characteristic-zero replay.
-- These independent exact coefficient receipts check both bounded residue
-- products, with cap larger than either possible product degree.
theorem cofactor_has_residue_inverse :
  ok [58, 32, 89, 72, 69, 61, 94] ordinary [15, 48, 13, 62, 74, 70, 54, 89] [55, 27, 9, 62, 39, 20, 7, 96] 16 = true := by decide

theorem product_gate_has_residue_inverse :
  ok [16, 36, 43, 19, 6, 22, 50] ordinary [44, 16, 48, 88, 46, 61, 1, 82] [64, 38, 94, 29, 79, 53, 43, 18] 16 = true := by decide

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSlackFourthTwinPortable

open RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSlackFourthTwinPortable
#print axioms cofactor_has_residue_inverse
#print axioms product_gate_has_residue_inverse
