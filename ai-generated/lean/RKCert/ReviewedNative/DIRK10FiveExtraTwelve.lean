module

public import RKCert.ReviewedNative.DIRK10FiveExtraTwelveFlagReplay
public import RKCert.ReviewedNative.FiniteScaledOrderCheck
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Exact DIRK10 with twelve stages and five extra primes

Only the literal tableau denominator is required to be a unit.  The
additional denominators used to row-reduce defect flags are not imposed
on the target.  The proof first recovers all integer moment identities
from the rational kernel certificate, then specializes those integers. -/

namespace RKResearch.Certified.DIRK10FiveExtraTwelveFlagReplay

open RKResearch Graded RationalFlagReplay FiniteRootedTree
open scoped Matrix

set_option maxHeartbeats 0
set_option maxRecDepth 50000

/-- The least common denominator of all literal tableau entries. -/
def denominator : ℤ := 14762353142762908220160000000

def integerA : Matrix (Fin 12) (Fin 12) ℤ :=
  fun i j => ((denominator : ℚ) * matrix packet i j).num

def integerWeights : Fin 12 → ℤ :=
  fun i => ((denominator : ℚ) * packet.b i).num

theorem integerA_lower : integerA.IsLowerTriangular := by
  intro i j hij
  change ((denominator : ℚ) * matrix packet i j).num = 0
  rw [lower_triangular hij]
  simp

theorem matrixNumeratorCheck :
    (List.finRange 12).all (fun i => (List.finRange 12).all (fun j =>
      decide ((integerA i j : ℚ) = (denominator : ℚ) * matrix packet i j))) = true := by
  decide +kernel

theorem weightNumeratorCheck :
    (List.finRange 12).all (fun i =>
      decide ((integerWeights i : ℚ) = (denominator : ℚ) * packet.b i)) = true := by
  decide +kernel

theorem integerA_Q :
    integerA.map (Int.castRingHom ℚ) = (denominator : ℚ) • matrix packet := by
  funext i j
  exact of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp matrixNumeratorCheck i (List.mem_finRange i)) j (List.mem_finRange j))

theorem integerWeights_Q :
    Int.castRingHom ℚ ∘ integerWeights = (denominator : ℚ) • packet.b := by
  funext i
  exact of_decide_eq_true (List.all_eq_true.mp weightNumeratorCheck i (List.mem_finRange i))

theorem cast_scaled_moment (t : FiniteRootedTree) :
    (Int.castRingHom ℚ) ((t.factorial : ℤ) * (integerWeights ⬝ᵥ Φ t integerA)) =
      ((denominator : ℚ) * (denominator : ℚ)^((t.order:ℕ)-1)) *
      ((t.factorial : ℚ) * (packet.b ⬝ᵥ Φ t (matrix packet))) := by
  simp only [map_mul,map_natCast,RingHom.map_dotProduct,map_Φ,integerA_Q,
    integerWeights_Q,Φ_matrix_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  ring

theorem integer_order_ten (t : FiniteRootedTree) (ht : (t.order:ℕ) ≤ 10) :
    (t.factorial : ℤ) * (integerWeights ⬝ᵥ Φ t integerA) =
      denominator * denominator^((t.order:ℕ)-1) := by
  apply (Int.cast_injective (α := ℚ))
  change (Int.castRingHom ℚ) _ = (Int.castRingHom ℚ) _
  rw [cast_scaled_moment,order_ten t ht,mul_one,map_mul,map_pow]
  rfl

section Target

variable {R : Type*} [CommRing R]

def A (d : R) : Matrix (Fin 12) (Fin 12) R :=
  d • integerA.map (Int.castRingHom R)

def weights (d : R) : Fin 12 → R :=
  d • (Int.castRingHom R ∘ integerWeights)

theorem A_lower (d : R) : (A d).IsLowerTriangular := by
  intro i j h
  change d * ((integerA i j : ℤ) : R) = 0
  rw [integerA_lower h]
  simp

theorem transport (d : R) (hd : (denominator : R)*d=1) :
    HasOrder 10 (A d) (weights d) := by
  let f := Int.castRingHom R
  have hfd : f denominator*d=1 := hd
  have hA : integerA.map f = f denominator • A d := by
    change integerA.map f = f denominator • (d • integerA.map f)
    rw [smul_smul,hfd,one_smul]
  have hb : f ∘ integerWeights = f denominator • weights d := by
    change f ∘ integerWeights = f denominator • (d • (f ∘ integerWeights))
    rw [smul_smul,hfd,one_smul]
  have hu : IsUnit (f denominator) := IsUnit.of_mul_eq_one _ hd
  exact hasOrder_of_scaled_moments f hA hb hu hu integer_order_ten

def nextTree : FiniteRootedTree := bushyTree 11

def mixedTree : FiniteRootedTree :=
  (FiniteRootedTree.butcherProduct .leaf (bushyTree 8)).addBush 2

def integerDefect (t : FiniteRootedTree) : ℤ :=
  (t.factorial : ℤ) * (integerWeights ⬝ᵥ Φ t integerA) - denominator^11

theorem integer_next_star : (5184000:ℤ) * integerDefect nextTree =
    (-1207) * denominator^11 := by decide +kernel

theorem integer_next_mixed : (3888000:ℤ) * integerDefect mixedTree =
    2711 * denominator^11 := by decide +kernel

theorem transport_defect (d : R) (hd : (denominator : R)*d=1)
    (t : FiniteRootedTree) (horder : (t.order:ℕ)-1=10)
    {k z : ℤ} (hint : k * integerDefect t = z * denominator^11) :
    (k:R) * ((t.factorial:R) * (weights d ⬝ᵥ Φ t (A d)) - 1) = (z:R) := by
  let f := Int.castRingHom R
  have hp : (f denominator)^11 * d^11 = 1 := by
    rw [← mul_pow]
    change ((denominator : R)*d)^11=1
    rw [hd, one_pow]
  have hmap0 := congrArg f hint
  unfold integerDefect at hmap0
  simp only [map_mul,map_sub,map_pow,map_natCast,RingHom.map_dotProduct,map_Φ] at hmap0
  simp only [A,weights,Φ_matrix_smul,horder,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  change _ = f z
  calc
     _ = f k * ((t.factorial:R) * ((f ∘ integerWeights) ⬝ᵥ Φ t (integerA.map f)) *
           d^11 - (f denominator)^11*d^11) := by
       rw [hp]
       simp only [f, Int.coe_castRingHom]
       ring
     _ = (f k * ((t.factorial:R) * ((f ∘ integerWeights) ⬝ᵥ Φ t (integerA.map f)) -
           (f denominator)^11)) * d^11 := by ring
     _ = f z := by rw [hmap0,mul_assoc,hp,mul_one]

theorem next_star_defect (d : R) (hd : (denominator : R)*d=1) :
    (5184000:R)*((nextTree.factorial:R)*(weights d ⬝ᵥ Φ nextTree (A d))-1)= -1207 := by
  simpa only [Int.cast_ofNat, Int.cast_neg] using
    transport_defect d hd nextTree (by decide) integer_next_star

theorem next_mixed_defect (d : R) (hd : (denominator : R)*d=1) :
    (3888000:R)*((mixedTree.factorial:R)*(weights d ⬝ᵥ Φ mixedTree (A d))-1)=2711 := by
  simpa only [Int.cast_ofNat] using
    transport_defect d hd mixedTree (by decide) integer_next_mixed

theorem not_order_eleven_of_inverse [Nontrivial R] (d : R) (hd : (denominator : R)*d=1) :
    ¬ HasOrder 11 (A d) (weights d) := by
  intro h
  have hs := next_star_defect d hd
  rw [h nextTree (by decide),sub_self,mul_zero] at hs
  have hm := next_mixed_defect d hd
  rw [h mixedTree (by decide),sub_self,mul_zero] at hm
  have hbez := congrArg (Int.castRingHom R)
    (by decide +kernel : (1141:ℤ)*(-1207)+508*2711=1)
  simp only [map_add,map_mul,map_one,Int.coe_castRingHom,Int.cast_ofNat,Int.cast_neg] at hbez
  rw [← hs, ← hm, mul_zero,mul_zero, add_zero] at hbez
  exact zero_ne_one hbez

theorem exists_exact_of_unit [Nontrivial R] (h : IsUnit (denominator:R)) :
    ∃ (T : Matrix (Fin 12) (Fin 12) R) (w : Fin 12 → R),
      T.IsLowerTriangular ∧ HasOrder 10 T w ∧ ¬ HasOrder 11 T w := by
  obtain ⟨d,hd⟩ := h.exists_right_inv
  exact ⟨A d,weights d,A_lower d,transport d hd,not_order_eleven_of_inverse d hd⟩

end Target
end RKResearch.Certified.DIRK10FiveExtraTwelveFlagReplay

#print axioms RKResearch.Certified.DIRK10FiveExtraTwelveFlagReplay.exists_exact_of_unit
