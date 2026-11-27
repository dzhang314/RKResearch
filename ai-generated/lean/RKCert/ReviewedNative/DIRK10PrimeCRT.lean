module

public import RKCert.ReviewedNative.DIRK10PrimeCRTMoments
public import RKCert.ReviewedNative.DIRK10PrimeCRTActionsA
public import RKCert.ReviewedNative.DIRK10PrimeCRTActionsC
public import RKCert.ReviewedNative.DIRK10PrimeCRTSilence
public import RKCert.ReviewedNative.DIRK10PrimeCRTProducts
public import RKCert.ReviewedNative.DIRKUniform
import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace RKResearch.Certified.DIRK10PrimeCRT
open RKResearch FiniteRootedTree RingFlagReplay
open scoped Matrix
set_option maxHeartbeats 0
set_option maxRecDepth 36000
set_option Elab.async false

theorem stepA (d : Nat) (hd : d < 9) : blockA d = true := by
  interval_cases d
  · exact actA0
  · exact actA1
  · exact actA2
  · exact actA3
  · exact actA4
  · exact actA5
  · exact actA6
  · exact actA7
  · exact actA8

theorem stepC (d : Nat) (hd : d < 9) : blockC d = true := by
  interval_cases d
  · exact actC0
  · exact actC1
  · exact actC2
  · exact actC3
  · exact actC4
  · exact actC5
  · exact actC6
  · exact actC7
  · exact actC8

theorem silence (d : Nat) (hd : d < 10) : blockS d = true := by
  interval_cases d
  · exact silent0
  · exact silent1
  · exact silent2
  · exact silent3
  · exact silent4
  · exact silent5
  · exact silent6
  · exact silent7
  · exact silent8
  · exact silent9

theorem primitiveReceipt (d : Nat) (hd : d < 9) : checkPrimitive packet d = true := by
  interval_cases d
  · exact primitive0
  · exact primitive1
  · exact primitive2
  · exact primitive3
  · exact primitive4
  · exact primitive5
  · exact primitive6
  · exact primitive7
  · exact primitive8

theorem scalarReceipt (d : Nat) (hd : d < 10) : checkScalar packet d = true := by
  interval_cases d
  · exact scalar0
  · exact scalar1
  · exact scalar2
  · exact scalar3
  · exact scalar4
  · exact scalar5
  · exact scalar6
  · exact scalar7
  · exact scalar8
  · exact scalar9

theorem products (d e : Nat) (h : d+e < 10) : blockP d e = true := by
  have hd : d < 10 := by omega
  interval_cases d
  · have he : e < 10 := by omega
    interval_cases e
    · exact product0_0
    · exact product0_1
    · exact product0_2
    · exact product0_3
    · exact product0_4
    · exact product0_5
    · exact product0_6
    · exact product0_7
    · exact product0_8
    · exact product0_9
  · have he : e < 9 := by omega
    interval_cases e
    · exact product1_0
    · exact product1_1
    · exact product1_2
    · exact product1_3
    · exact product1_4
    · exact product1_5
    · exact product1_6
    · exact product1_7
    · exact product1_8
  · have he : e < 8 := by omega
    interval_cases e
    · exact product2_0
    · exact product2_1
    · exact product2_2
    · exact product2_3
    · exact product2_4
    · exact product2_5
    · exact product2_6
    · exact product2_7
  · have he : e < 7 := by omega
    interval_cases e
    · exact product3_0
    · exact product3_1
    · exact product3_2
    · exact product3_3
    · exact product3_4
    · exact product3_5
    · exact product3_6
  · have he : e < 6 := by omega
    interval_cases e
    · exact product4_0
    · exact product4_1
    · exact product4_2
    · exact product4_3
    · exact product4_4
    · exact product4_5
  · have he : e < 5 := by omega
    interval_cases e
    · exact product5_0
    · exact product5_1
    · exact product5_2
    · exact product5_3
    · exact product5_4
  · have he : e < 4 := by omega
    interval_cases e
    · exact product6_0
    · exact product6_1
    · exact product6_2
    · exact product6_3
  · have he : e < 3 := by omega
    interval_cases e
    · exact product7_0
    · exact product7_1
    · exact product7_2
  · have he : e < 2 := by omega
    interval_cases e
    · exact product8_0
    · exact product8_1
  · have he : e < 1 := by omega
    interval_cases e
    · exact product9_0

theorem receipts : Receipts 10 packet := by
  refine ⟨node,?_,?_,?_,?_,?_,scalarReceipt⟩
  · intro d hd i
    exact List.all_eq_true.mp (stepA d (by omega)) i (List.mem_finRange i)
  · intro d hd i
    exact List.all_eq_true.mp (stepC d (by omega)) i (List.mem_finRange i)
  · intro d e hd i j
    exact List.all_eq_true.mp (List.all_eq_true.mp (products d e hd) i
      (List.mem_finRange i)) j (List.mem_finRange j)
  · intro d hd
    exact primitiveReceipt d (by omega)
  · intro d hd i
    exact List.all_eq_true.mp (silence d hd) i (List.mem_finRange i)

def A : Matrix (Fin 11) (Fin 11) F := matrix packet
def b : Fin 11 → F := packet.b

theorem paid : HasOrder 10 A b := RingFlagReplay.order receipts

theorem lowerA : A.IsLowerTriangular := RingFlagReplay.lower packet

theorem next_unit : IsUnit (((bushyTree 11).factorial:F)*(b ⬝ᵥ Φ (bushyTree 11) A)-1) := by
  have hu : IsUnit (bushResidual packet 10) := by
    rw [next_star]
    exact IsUnit.of_mul_eq_one starInv star_inv
  rw [bushResidual,output_eq,node_eq receipts,Graded.row_apply] at hu
  have hf : (((bushyTree 11).factorial : ℕ) : F) = (11 : ℕ) := by decide +kernel
  have hg : ((11 : ℕ+) : ℕ)-1=10 := by decide +kernel
  rw [Φ_bushyTree, hf, hg]
  exact hu

/-- One literal width-eleven tableau gives order ten and a unit eleventh
bush over each nonzero ring of any characteristic dividing the combined modulus. -/
theorem exists_paid_of_dvd (R : Type*) [CommRing R] (n : Nat) [CharP R n]
    (h : n ∣ modulus) :
    ∃ (U : Matrix (Fin 11) (Fin 11) R) (w : Fin 11 → R),
      U.IsLowerTriangular ∧ HasOrder 10 U w ∧
      IsUnit (((bushyTree 11).factorial:R)*(w ⬝ᵥ Φ (bushyTree 11) U)-1) := by
  let f := ZMod.castHom h R
  refine ⟨A.map f, f ∘ b, ?_, paid.map f, ?_⟩
  · intro i j hij
    change f (A i j)=0
    rw [lowerA hij, map_zero]
  · simpa only [map_sub,map_mul,map_natCast,map_one,RingHom.map_dotProduct,map_Φ] using
      next_unit.map f

theorem exists_exact_of_dvd (R : Type*) [CommRing R] [Nontrivial R] (n : Nat) [CharP R n]
    (h : n ∣ modulus) :
    ∃ (U : Matrix (Fin 11) (Fin 11) R) (w : Fin 11 → R),
      U.IsLowerTriangular ∧ HasOrder 10 U w ∧ ¬ HasOrder 11 U w := by
  obtain ⟨U,w,hL,hOrder,hUnit⟩ := exists_paid_of_dvd R n h
  refine ⟨U,w,hL,hOrder,?_⟩
  intro hNext
  rw [hNext (bushyTree 11) (by decide),sub_self] at hUnit
  exact hUnit.ne_zero rfl

theorem exists_exact_prime_in_list (K : Type*) [Field K] (p : Nat) [CharP K p]
    (hp : p ∈ primes) :
    ∃ (U : Matrix (Fin 11) (Fin 11) K) (w : Fin 11 → K),
      U.IsLowerTriangular ∧ HasOrder 10 U w ∧ ¬ HasOrder 11 U w :=
  exists_exact_of_dvd K p (prime_divides hp)

theorem exists_exact_char_59 (R : Type*) [CommRing R] [Nontrivial R] [CharP R 59] :
    ∃ (U : Matrix (Fin 11) (Fin 11) R) (w : Fin 11 → R),
      U.IsLowerTriangular ∧ HasOrder 10 U w ∧ ¬ HasOrder 11 U w :=
  exists_exact_of_dvd R 59 (prime_divides (by decide))

theorem exists_exact_char_3481 (R : Type*) [CommRing R] [Nontrivial R] [CharP R 3481] :
    ∃ (U : Matrix (Fin 11) (Fin 11) R) (w : Fin 11 → R),
      U.IsLowerTriangular ∧ HasOrder 10 U w ∧ ¬ HasOrder 11 U w :=
  exists_exact_of_dvd R 3481 squared_59_divides

theorem minimum_stages_floor {R : Type*} [CommRing R] [Nontrivial R] {s : Nat}
    {U : Matrix (Fin s) (Fin s) R} {w : Fin s → R}
    (hL : U.IsLowerTriangular) (ho : HasOrder 10 U w) : 11 ≤ s :=
  ho.dirk_uniform_stages hL (by decide)

end RKResearch.Certified.DIRK10PrimeCRT
