module

public import RKCert.ReviewedNative.DIRK12MidpointPrimeCRTChecks

@[expose] public section

/-! Actual width fifteen and a unit order-thirteen witness over the combined
prime-power modulus and every commutative characteristic divisor. This is
a finite literal certificate, not an assertion of unbounded Hensel lifting. -/
namespace RKResearch.Certified.DIRK12MidpointPrimeCRT

open RKResearch DualSupport12VectorReplay
open scoped Matrix FiniteRootedTree

def A : Matrix (Fin 15) (Fin 15) K := matrix packet
def b : Fin 15 → K := packet.b

theorem paid : HasOrder 12 A b := order_twelve receipts units

theorem lowerA : A.IsLowerTriangular := lower packet

theorem unit_next : IsUnit (((nextTree.factorial:Nat):K)*(b ⬝ᵥ Φ nextTree A)-1) :=
  nextUnit receipts

theorem paid_of_dvd (R : Type*) [CommRing R] (n : Nat) [CharP R n] (h : n ∣ M) :
    ∃ (U : Matrix (Fin 15) (Fin 15) R) (w : Fin 15 → R),
      U.IsLowerTriangular ∧ U 0 0 = 0 ∧ IsUnit (U 1 1) ∧ HasOrder 12 U w ∧
        IsUnit (((nextTree.factorial : Nat) : R) * (w ⬝ᵥ Φ nextTree U) - 1) := by
  let f : K →+* R := ZMod.castHom h R
  refine ⟨A.map f, f ∘ b, ?_, ?_, ?_, paid.map f, ?_⟩
  · intro i j hij
    change f (A i j) = 0
    rw [lowerA hij, map_zero]
  · change f (matrix packet 0 0) = 0
    rw [receipts.firstDiag, map_zero]
  · exact (IsUnit.of_mul_eq_one packet.diagInverse receipts.diagUnit).map f
  · simpa only [map_sub,map_mul,map_natCast,map_one,RingHom.map_dotProduct,map_Φ] using
      unit_next.map f

theorem exact_of_dvd (R : Type*) [CommRing R] [Nontrivial R] (n : Nat) [CharP R n]
    (h : n ∣ M) :
    ∃ (U : Matrix (Fin 15) (Fin 15) R) (w : Fin 15 → R),
      U.IsLowerTriangular ∧ U 0 0 ≠ U 1 1 ∧ HasOrder 12 U w ∧ ¬ HasOrder 13 U w := by
  obtain ⟨U,w,hL,h0,h1,hOrder,hU⟩ := paid_of_dvd R n h
  refine ⟨U,w,hL,h0 ▸ h1.ne_zero.symm,hOrder,?_⟩
  intro hNext
  exact hU.ne_zero (sub_eq_zero.mpr (hNext nextTree next_size))

theorem exact_of_modulus_zero (R : Type*) [CommRing R] [Nontrivial R]
    (h : ((M : Nat) : R) = 0) :
    ∃ (U : Matrix (Fin 15) (Fin 15) R) (w : Fin 15 → R),
      U.IsLowerTriangular ∧ U 0 0 ≠ U 1 1 ∧ HasOrder 12 U w ∧ ¬ HasOrder 13 U w := by
  obtain ⟨n, hChar⟩ := CharP.exists R
  let _ : CharP R n := hChar
  exact exact_of_dvd R n ((CharP.cast_eq_zero_iff R n M).mp h)

theorem divisor_131 (e : Nat) (h : e ≤ exponent) : 131^e ∣ M := by
  exact (Nat.pow_dvd_pow 131 h).trans (pow_dvd_pow_of_dvd (by decide +kernel) exponent)

theorem divisor_149 (e : Nat) (h : e ≤ exponent) : 149^e ∣ M := by
  exact (Nat.pow_dvd_pow 149 h).trans (pow_dvd_pow_of_dvd (by decide +kernel) exponent)

theorem exact_131 :
    ∃ (U : Matrix (Fin 15) (Fin 15) (ZMod 131)) (w : Fin 15 → ZMod 131),
      U.IsLowerTriangular ∧ U 0 0 ≠ U 1 1 ∧ HasOrder 12 U w ∧ ¬ HasOrder 13 U w := by
  let _ : Fact (1 < 131) := ⟨by decide +kernel⟩
  exact exact_of_dvd (ZMod 131) 131 (by decide +kernel)

theorem exact_149 :
    ∃ (U : Matrix (Fin 15) (Fin 15) (ZMod 149)) (w : Fin 15 → ZMod 149),
      U.IsLowerTriangular ∧ U 0 0 ≠ U 1 1 ∧ HasOrder 12 U w ∧ ¬ HasOrder 13 U w := by
  let _ : Fact (1 < 149) := ⟨by decide +kernel⟩
  exact exact_of_dvd (ZMod 149) 149 (by decide +kernel)

end RKResearch.Certified.DIRK12MidpointPrimeCRT

#print axioms RKResearch.Certified.DIRK12MidpointPrimeCRT.paid
#print axioms RKResearch.Certified.DIRK12MidpointPrimeCRT.unit_next
#print axioms RKResearch.Certified.DIRK12MidpointPrimeCRT.paid_of_dvd
#print axioms RKResearch.Certified.DIRK12MidpointPrimeCRT.exact_of_modulus_zero
#print axioms RKResearch.Certified.DIRK12MidpointPrimeCRT.exact_131
#print axioms RKResearch.Certified.DIRK12MidpointPrimeCRT.exact_149
