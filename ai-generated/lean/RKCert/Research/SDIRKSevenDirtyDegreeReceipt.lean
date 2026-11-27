module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Int.ModEq

@[expose] public section

/-! # Arithmetic checks used in the nine-stage dirty projection certificate

This module certifies the factor-degree intersection and the bounded CRT
uniqueness rule. It does not re-run the polynomial resultant or the
Rabin verifications of the six modular factorizations. -/
namespace RKResearch.Certified.SDIRKSevenDirtyDegreeReceipt

def subsetDegrees : List ℕ → List ℕ
  | [] => [0]
  | d :: ds =>
      let r := subsetDegrees ds
      r ++ r.map (d + ·)

def degreePartitions : List (List ℕ) :=
  [[1,2,2,5,20,68,78,148],
   [2,13,25,142,142],
   [2,4,5,7,23,91,192],
   [2,6,8,15,54,57,182],
   [2,2,5,5,7,10,293],
   [4,7,29,284]]

def allowed (d : ℕ) : Bool :=
  degreePartitions.all (fun ds => (subsetDegrees ds).contains d)

set_option maxRecDepth 8192 in
/-- Any factor degree consistent with the six listed reductions is
either zero or the full degree. The modular factors themselves are
verified by the separate finite-arithmetic checker. -/
theorem only_degrees :
    ∀ d : Fin 325, allowed d.val = true → d.val = 0 ∨ d.val = 324 := by
  decide +kernel

/-- Unique signed coefficients once the CRT modulus exceeds twice
the proved magnitude bound. -/
theorem bounded_crt_unique {a b M : ℤ} {B : ℕ}
    (ha : a.natAbs ≤ B) (hb : b.natAbs ≤ B) (hm : 2*B < M.natAbs)
    (h : a ≡ b [ZMOD M]) : a=b := by
  apply sub_eq_zero.mp
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (Int.modEq_iff_dvd.mp h.symm)
  have t := Int.natAbs_add_le a (-b)
  rw [Int.natAbs_neg] at t
  change (a-b).natAbs ≤ a.natAbs+b.natAbs at t
  omega

end RKResearch.Certified.SDIRKSevenDirtyDegreeReceipt
