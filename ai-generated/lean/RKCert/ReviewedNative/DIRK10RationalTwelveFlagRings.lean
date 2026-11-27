module

public import RKCert.ReviewedNative.DIRK10RationalTwelveFlagReplay
public import RKCert.ReviewedNative.FiniteScaledOrderCheck
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Ring specialization of the exact twelve-stage rational DIRK10

Only the literal tableau denominator is required to be a unit.  The
additional denominators used to row-reduce defect flags are not imposed
on the target.  The proof first recovers all integer moment identities
from the rational kernel certificate, then specializes those integers. -/

namespace RKResearch.Certified.DIRK10RationalTwelveFlagReplay

open RKResearch Graded RationalFlagReplay FiniteRootedTree
open scoped Matrix

set_option maxHeartbeats 0
set_option maxRecDepth 50000

/-- The least common denominator of all literal tableau entries. -/
def denominator : ℤ := 101588047290852467338246934187117072000

theorem denominator_factored :
    denominator = 2^7 * 3^5 * 5^3 * 7 * 11 * 17^2 * 19 * 151 * 173 * 607 *
      653 * 1063 * 1499 * 1553^3 := by decide +kernel

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

def nextTree : FiniteRootedTree := bushyTree 11

theorem next_rational_residual :
    (nextTree.factorial : ℚ) * (packet.b ⬝ᵥ Φ nextTree (matrix packet)) - 1 =
      1/2488320 := by
  rw [← next_star]
  rw [nextTree,Φ_bushyTree,factorial_bushyTree]
  rw [bushResidual,output_eq,node_eq receipts,row_apply]
  rfl

theorem integer_next :
    (2488320 : ℤ) * ((nextTree.factorial : ℤ) * (integerWeights ⬝ᵥ Φ nextTree integerA) -
      denominator * denominator^10) = denominator * denominator^10 := by
  apply (Int.cast_injective (α := ℚ))
  change (Int.castRingHom ℚ) _ = (Int.castRingHom ℚ) _
  rw [map_mul,map_sub,cast_scaled_moment,map_mul,map_pow,
    show ((nextTree.order:ℕ)-1)=10 by decide]
  change (2488320 : ℚ) *
      (((denominator : ℚ) * (denominator : ℚ)^10) *
        ((nextTree.factorial : ℚ) * (packet.b ⬝ᵥ Φ nextTree (matrix packet))) -
          ((denominator : ℚ) * (denominator : ℚ)^10)) =
      (denominator : ℚ) * (denominator : ℚ)^10
  have hf := next_rational_residual
  calc
    _ = ((denominator : ℚ) * (denominator : ℚ)^10) *
        ((2488320 : ℚ) * ((nextTree.factorial : ℚ) *
          (packet.b ⬝ᵥ Φ nextTree (matrix packet)) - 1)) := by ring
    _ = (denominator : ℚ) * (denominator : ℚ)^10 := by
      rw [hf, show (2488320 : ℚ) * (1 / 2488320) = 1 by norm_num, mul_one]

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

theorem transport_failure [Nontrivial R] (d : R) (hd : (denominator : R)*d=1) :
    ¬ HasOrder 11 (A d) (weights d) := by
  let f := Int.castRingHom R
  have hfd : f denominator*d=1 := hd
  have hA : integerA.map f = f denominator • A d := by
    change integerA.map f = f denominator • (d • integerA.map f)
    rw [smul_smul,hfd,one_smul]
  have hb : f ∘ integerWeights = f denominator • weights d := by
    change f ∘ integerWeights = f denominator • (d • (f ∘ integerWeights))
    rw [smul_smul,hfd,one_smul]
  intro ho
  have ordered := ho nextTree (by decide)
  have hmoment : (nextTree.factorial : R) * (weights d ⬝ᵥ Φ nextTree (A d)) = 1 := ordered
  have hcast := congrArg f integer_next
  simp only [map_mul,map_sub,map_pow,map_natCast,RingHom.map_dotProduct,map_Φ,
    hA,hb,Φ_matrix_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul,
    show ((nextTree.order:ℕ)-1)=10 by decide] at hcast
  have he :
      (nextTree.factorial : R) *
        (f denominator ^ 10 * (f denominator * (weights d ⬝ᵥ Φ nextTree (A d)))) =
          f denominator * f denominator ^ 10 := by
    calc
      _ = f denominator * f denominator ^ 10 *
           ((nextTree.factorial : R) * (weights d ⬝ᵥ Φ nextTree (A d))) := by ring
      _ = _ := by rw [hmoment,mul_one]
  rw [he,sub_self,mul_zero] at hcast
  have hu : IsUnit (f denominator) := IsUnit.of_mul_eq_one _ hfd
  exact (hu.mul (hu.pow 10)).ne_zero hcast.symm

/-- The literal twelve-stage algebraic identities specialize to any
nontrivial commutative ring in which the tableau denominator is a unit. -/
theorem exists_exact_of_unit [Nontrivial R] (h : IsUnit (denominator : R)) :
    ∃ (T : Matrix (Fin 12) (Fin 12) R) (w : Fin 12 → R),
      T.IsLowerTriangular ∧ HasOrder 10 T w ∧ ¬ HasOrder 11 T w := by
  obtain ⟨d,hd⟩ := h.exists_right_inv
  exact ⟨A d,weights d,A_lower d,transport d hd,transport_failure d hd⟩

end Target
end RKResearch.Certified.DIRK10RationalTwelveFlagReplay

#print axioms RKResearch.Certified.DIRK10RationalTwelveFlagReplay.exists_exact_of_unit
