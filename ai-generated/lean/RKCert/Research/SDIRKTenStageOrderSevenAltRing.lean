module

public import RKCert.ReviewedNative.FiniteScaledOrderCheck
public import Mathlib.Algebra.Field.Rat
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Alternative ten-stage strict SDIRK of exact order seven

All rooted conditions are replayed on integer numerators. The diagonal
is the inverse of four. The eighth bush alone has a unit discrepancy.
This tableau has denominator primes complementary to the diagonal-1/5 witness.
-/

namespace RKResearch.Certified.SDIRKTenStageOrderSevenAltRing
open FiniteRootedTree
open scoped Matrix

/-- The literal numerator matrix $2913563520 A$. -/
def AInt : Matrix (Fin 10) (Fin 10) ℤ :=
  !![728390880,0,0,0,0,0,0,0,0,0;
     728390880,728390880,0,0,0,0,0,0,0,0;
     -1456781760,728390880,728390880,0,0,0,0,0,0,0;
     971187840,-485593920,242796960,728390880,0,0,0,0,0,0;
     0,0,-728390880,0,728390880,0,0,0,0,0;
     -242796960,121398480,456520260,-182097720,-153024060,728390880,0,0,0,0;
     25250883840,-12625441920,687560160,13111035840,-930357120,-23308508160,728390880,0,0,0;
     -1499514024960,749757012480,265416449760,-658465355520,-241136753760,1398510489600,-18209772000,728390880,0,0;
     679103097120,-339551548560,-24067248660,294816208680,0,-615344615424,7875726390,81943974,728390880,0;
     -3884751360,1942375680,-655784640,-1628436600,898092090,4932694368,-153461385,-38073,6091680,728390880]

/-- The literal numerator output $39690 b$. -/
def bInt : Fin 10 → ℤ := ![0,0,0,6132,3213,13608,3402,-1,-56,13392]

private theorem numerator_triangular : AInt.IsLowerTriangular := by
  change ∀ i j : Fin 10, i < j → AInt i j = 0
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem numerator_diagonal (i : Fin 10) : AInt i i = 728390880 :=
  (by decide +kernel : ∀ i : Fin 10, AInt i i = 728390880) i

private def paidTree (t : FiniteRootedTree) : Bool :=
  decide ((t.factorial : ℤ) * (bInt ⬝ᵥ replayStage (fun v => AInt *ᵥ v) t) =
    39690 * 2913563520 ^ ((t.order : ℕ) - 1))

private theorem all_true_parts (k : ℕ) (trees : List FiniteRootedTree)
    (head : (trees.take k).all paidTree = true)
    (tail : (trees.drop k).all paidTree = true) : trees.all paidTree = true := by
  calc
    trees.all paidTree = (trees.take k ++ trees.drop k).all paidTree := by
      rw [List.take_append_drop]
    _ = true := by simp only [List.all_append, head, tail, Bool.true_and]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup0 : (treesOfOrderSucc 0).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup1 : (treesOfOrderSucc 1).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup2 : (treesOfOrderSucc 2).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup3 : (treesOfOrderSucc 3).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup4 : (treesOfOrderSucc 4).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup5_part0 : ((treesOfOrderSucc 5).take 14).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup5_part1 : (((treesOfOrderSucc 5).drop 14).take 14).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup5_part2 : (((treesOfOrderSucc 5).drop 14).drop 14).all paidTree = true := by
  decide +kernel

private theorem paidGroup5 : (treesOfOrderSucc 5).all paidTree = true :=
  (all_true_parts 14 _ paidGroup5_part0 (all_true_parts 14 _ paidGroup5_part1 paidGroup5_part2))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup6_part0 : ((treesOfOrderSucc 6).take 14).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup6_part1 : (((treesOfOrderSucc 6).drop 14).take 14).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup6_part2 : ((((treesOfOrderSucc 6).drop 14).drop 14).take 14).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup6_part3 : (((((treesOfOrderSucc 6).drop 14).drop 14).drop 14).take 14).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup6_part4 : ((((((treesOfOrderSucc 6).drop 14).drop 14).drop 14).drop 14).take 14).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup6_part5 : (((((((treesOfOrderSucc 6).drop 14).drop 14).drop 14).drop 14).drop 14).take 14).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup6_part6 : ((((((((treesOfOrderSucc 6).drop 14).drop 14).drop 14).drop 14).drop 14).drop 14).take 14).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup6_part7 : (((((((((treesOfOrderSucc 6).drop 14).drop 14).drop 14).drop 14).drop 14).drop 14).drop 14).take 14).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup6_part8 : ((((((((((treesOfOrderSucc 6).drop 14).drop 14).drop 14).drop 14).drop 14).drop 14).drop 14).drop 14).take 14).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem paidGroup6_part9 : ((((((((((treesOfOrderSucc 6).drop 14).drop 14).drop 14).drop 14).drop 14).drop 14).drop 14).drop 14).drop 14).all paidTree = true := by
  decide +kernel

private theorem paidGroup6 : (treesOfOrderSucc 6).all paidTree = true :=
  (all_true_parts 14 _ paidGroup6_part0 (all_true_parts 14 _ paidGroup6_part1 (all_true_parts 14 _ paidGroup6_part2 (all_true_parts 14 _ paidGroup6_part3 (all_true_parts 14 _ paidGroup6_part4 (all_true_parts 14 _ paidGroup6_part5 (all_true_parts 14 _ paidGroup6_part6 (all_true_parts 14 _ paidGroup6_part7 (all_true_parts 14 _ paidGroup6_part8 paidGroup6_part9)))))))))

private theorem paidGroup (n : Fin 7) :
    (treesOfOrderSucc n.val).all paidTree = true := by
  fin_cases n
  · exact paidGroup0
  · exact paidGroup1
  · exact paidGroup2
  · exact paidGroup3
  · exact paidGroup4
  · exact paidGroup5
  · exact paidGroup6

private theorem checked :
    checkScaledOrder (fun v => AInt *ᵥ v) (fun v => bInt ⬝ᵥ v) 2913563520 39690 7 = true := by
  change (List.range 7).all (fun n => (treesOfOrderSucc n).all paidTree) = true
  apply List.all_eq_true.mpr
  intro n hn
  exact paidGroup ⟨n, List.mem_range.mp hn⟩

private theorem numerator_bush_eight :
    448 * (((bushyTree 8).factorial : ℤ) * (bInt ⬝ᵥ Φ (bushyTree 8) AInt)) =
      449 * (39690 * (2913563520 : ℤ)^7) := by
  rw [factorial_bushyTree, Φ_bushyTree]
  decide +kernel

variable {R : Type*} [CommRing R]

private theorem unitOfNatDvd {d m : ℕ} (h : d ∣ m) (hm : IsUnit (m : R)) :
    IsUnit (d : R) := by
  obtain ⟨e,he⟩ := h
  apply isUnit_of_dvd_unit _ hm
  exact ⟨(e : R), by simpa only [Nat.cast_mul] using congrArg ((↑) : ℕ → R) he⟩

/-- The new rational tableau specializes whenever its stage denominator
is a unit. The weight denominator divides a power of the stage denominator. -/
theorem exists_exact_of_stageDen_unit [Nontrivial R] (h : IsUnit (2913563520 : R)) :
    ∃ (A : Matrix (Fin 10) (Fin 10) R) (b : Fin 10 → R) (γ : R),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ IsUnit γ ∧ (4 : R) * γ = 1 ∧
        HasOrder 7 A b ∧ ¬ HasOrder 8 A b := by
  have hpow : IsUnit (((2913563520 : ℕ)^4 : ℕ) : R) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using h.pow 4
  have he : IsUnit (39690 : R) := by
    simpa only [Nat.cast_ofNat] using unitOfNatDvd (R := R) (d := 39690) (by decide) hpow
  obtain ⟨d,hd'⟩ := h
  obtain ⟨e,he'⟩ := he
  let f := Int.castRingHom R
  let A : Matrix (Fin 10) (Fin 10) R := Matrix.of fun i j => (↑d⁻¹ : R) * f (AInt i j)
  let b : Fin 10 → R := fun i => (↑e⁻¹ : R) * f (bInt i)
  let γ : R := (↑d⁻¹ : R) * 728390880
  have hAu : AInt.map f = f 2913563520 • A := by
    ext i j
    simp only [map_ofNat]
    change f (AInt i j) = (2913563520 : R) * ((↑d⁻¹ : R) * f (AInt i j))
    rw [←hd', ←mul_assoc]; simp
  have hbu : f ∘ bInt = f 39690 • b := by
    funext i
    simp only [map_ofNat]
    change f (bInt i) = (39690 : R) * ((↑e⁻¹ : R) * f (bInt i))
    rw [←he', ←mul_assoc]; simp
  have hd : IsUnit (f 2913563520) := by rw [map_ofNat, ←hd']; exact d.isUnit
  have he : IsUnit (f 39690) := by rw [map_ofNat, ←he']; exact e.isUnit
  have h4 : (4 : R) * γ = 1 := by
    have hdi : (2913563520 : R) * (↑d⁻¹ : R) = 1 := by rw [←hd']; simp
    change (4 : R) * ((↑d⁻¹ : R) * 728390880) = 1
    linear_combination (norm := ring) hdi
  refine ⟨A,b,γ,?_,?_,IsUnit.of_mul_eq_one (4:R) ((mul_comm _ _).trans h4),h4,?_,?_⟩
  · intro i j hij
    change (↑d⁻¹:R) * f (AInt i j) = 0
    rw [numerator_triangular hij, map_zero, mul_zero]
  · intro i
    change (↑d⁻¹:R) * f (AInt i i) = γ
    rw [numerator_diagonal, map_ofNat]
  · exact hasOrder_of_scaled_check f (fun _ => rfl) (fun _ => rfl)
      hAu hbu hd he checked
  · intro h8
    let Ω : R := (39690 : R) * (2913563520 : R)^7
    have hΩ : IsUnit Ω := by
      simpa only [Ω, map_ofNat] using he.mul (hd.pow 7)
    have hPaid (t : FiniteRootedTree) (ht : (t.order : ℕ) = 8) :
        f ((t.factorial : ℤ) * (bInt ⬝ᵥ Φ t AInt)) = Ω := by
      have hp : (t.factorial : R) * (b ⬝ᵥ Φ t A) = 1 := h8 t (by rw [ht])
      simp only [map_mul, map_natCast, RingHom.map_dotProduct, RKResearch.map_Φ,
        hAu, hbu, Φ_matrix_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, ht, map_ofNat]
      change (t.factorial : R) * ((2913563520 : R)^7 *
        ((39690 : R) * (b ⬝ᵥ Φ t A))) = Ω
      linear_combination (norm := ring) Ω * hp
    have hB := congrArg f numerator_bush_eight
    rw [map_mul, hPaid _ (by simp [order_bushyTree])] at hB
    simp only [map_mul, map_pow, map_ofNat] at hB
    change (448 : R) * Ω = 449 * Ω at hB
    exact hΩ.ne_zero (by linear_combination (norm := ring) -hB)

/-- A convenient sufficient unit premise: the paid factorial and the
two explicitly identified extra prime factors. -/
theorem exists_exact_of_paid_and_extra [Nontrivial R]
    (h : IsUnit (5040 : R)) (he : IsUnit ((31 * 37) : R)) :
    ∃ (A : Matrix (Fin 10) (Fin 10) R) (b : Fin 10 → R) (γ : R),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ IsUnit γ ∧ (4 : R) * γ = 1 ∧
        HasOrder 7 A b ∧ ¬ HasOrder 8 A b := by
  have hu : IsUnit ((((5040 * 31 * 37)^3 : ℕ)) : R) := by
    simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
    rw [show (5040 : R)*31*37 = 5040*(31*37) by ring]
    exact (h.mul he).pow 3
  exact exists_exact_of_stageDen_unit (unitOfNatDvd (d := 2913563520) (by decide) hu)

/-- The complementary rational ten-stage witness at diagonal one quarter. -/
theorem exists_exact_rational :
    ∃ (A : Matrix (Fin 10) (Fin 10) ℚ) (b : Fin 10 → ℚ),
      A.IsLowerTriangular ∧ (∀ i, A i i = 1/4) ∧
        HasOrder 7 A b ∧ ¬ HasOrder 8 A b := by
  obtain ⟨A,b,γ,ha,hdiag,_,h4,ho,he⟩ :=
    exists_exact_of_stageDen_unit (R := ℚ) (isUnit_iff_ne_zero.mpr (by decide +kernel))
  have hγ : γ = (1/4 : ℚ) := mul_left_cancel₀ (by decide : (4:ℚ) ≠ 0)
    (h4.trans (by decide +kernel))
  exact ⟨A,b,ha,fun i => (hdiag i).trans hγ,ho,he⟩

end RKResearch.Certified.SDIRKTenStageOrderSevenAltRing

