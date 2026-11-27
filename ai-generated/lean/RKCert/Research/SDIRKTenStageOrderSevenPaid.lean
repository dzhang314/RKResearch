module

public import RKCert.ReviewedNative.FiniteScaledOrderCheck
public import Mathlib.Algebra.Field.Rat
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Ten stages of exact strict SDIRK order seven over every paid ring

All rooted conditions are replayed on integer numerators. The diagonal
is the inverse of four. Both scales divide powers of 7!, and two
small eighth-order discrepancies cannot vanish simultaneously in a
nonzero ring. The construction needs no field or local-ring hypothesis.
-/

namespace RKResearch.Certified.SDIRKTenStageOrderSevenPaid
open FiniteRootedTree
open scoped Matrix

/-- The literal numerator matrix $4423680 A$. -/
def AInt : Matrix (Fin 10) (Fin 10) ℤ :=
  !![1105920,0,0,0,0,0,0,0,0,0;
     5529600,1105920,0,0,0,0,0,0,0,0;
     -1769472,663552,1105920,0,0,0,0,0,0,0;
     4128768,49152,-860160,1105920,0,0,0,0,0,0;
     -884736,-221184,-552960,552960,1105920,0,0,0,0,0;
     1241948160,311470080,779658240,-771056640,-1554278400,1105920,0,0,0,0;
     608256,-32256,-264960,-149760,921600,23040,1105920,0,0,0;
     -200613888,-366692352,-1233269760,1048826880,1645701120,2949120,-902430720,1105920,0,0;
     444456,-23606,-193735,195765,383940,-3990,-803040,210,1105920,0;
     -1382184,73334,602215,-498705,0,-5070,1211040,-630,2211840,1105920]

/-- The literal numerator output $52920 b$. -/
def bInt : Fin 10 → ℤ := ![0,0,0,4221,4221,-1,7616,-1,18432,18432]

private theorem numerator_triangular : AInt.IsLowerTriangular := by
  change ∀ i j : Fin 10, i < j → AInt i j = 0
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem numerator_diagonal (i : Fin 10) : AInt i i = 1105920 :=
  (by decide +kernel : ∀ i : Fin 10, AInt i i = 1105920) i

private def paidTree (t : FiniteRootedTree) : Bool :=
  decide ((t.factorial : ℤ) * (bInt ⬝ᵥ replayStage (fun v => AInt *ᵥ v) t) =
    52920 * 4423680 ^ ((t.order : ℕ) - 1))

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
    checkScaledOrder (fun v => AInt *ᵥ v) (fun v => bInt ⬝ᵥ v) 4423680 52920 7 = true := by
  change (List.range 7).all (fun n => (treesOfOrderSucc n).all paidTree) = true
  apply List.all_eq_true.mpr
  intro n hn
  exact paidGroup ⟨n, List.mem_range.mp hn⟩

-- These are ordinary rooted trees at order eight, not manufactured tests.
-- The first is a stem over a root with leaf and five-vertex bush children.
private def treeA : FiniteRootedTree :=
  .butcherProduct .leaf (.butcherProduct (bushyTree 2) (bushyTree 5))

-- The second is a five-vertex bush under three successive stems.
private def treeB : FiniteRootedTree :=
  .butcherProduct .leaf (.butcherProduct .leaf (.butcherProduct .leaf (bushyTree 5)))

private theorem orderA : (treeA.order : ℕ) = 8 := by decide +kernel
private theorem orderB : (treeB.order : ℕ) = 8 := by decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem numerator_A :
    576 * ((treeA.factorial : ℤ) * (bInt ⬝ᵥ Φ treeA AInt)) =
      631 * (52920 * (4423680 : ℤ)^7) := by
  simp only [treeA, Φ, Φ_bushyTree, one_mul]
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem numerator_B :
    96 * ((treeB.factorial : ℤ) * (bInt ⬝ᵥ Φ treeB AInt)) =
      -5 * (52920 * (4423680 : ℤ)^7) := by
  simp only [treeB, Φ, Φ_bushyTree, one_mul]
  decide +kernel

variable {R : Type*} [CommRing R]

private theorem unitOfNatDvd {d m : ℕ} (h : d ∣ m) (hm : IsUnit (m : R)) :
    IsUnit (d : R) := by
  obtain ⟨e,he⟩ := h
  apply isUnit_of_dvd_unit _ hm
  exact ⟨(e : R), by simpa only [Nat.cast_mul] using congrArg ((↑) : ℕ → R) he⟩

/-- A single exact-order-seven strict SDIRK over every nonzero
commutative ring in which 7! is a unit. The common unit diagonal
is characterized by 4 times the diagonal being one. -/
theorem exists_exact [Nontrivial R] (h : IsUnit (5040 : R)) :
    ∃ (A : Matrix (Fin 10) (Fin 10) R) (b : Fin 10 → R) (γ : R),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ IsUnit γ ∧ (4 : R) * γ = 1 ∧
        HasOrder 7 A b ∧ ¬ HasOrder 8 A b := by
  have hpow : IsUnit (((5040 : ℕ)^4 : ℕ) : R) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using h.pow 4
  have hD : IsUnit (4423680 : R) := by
    simpa only [Nat.cast_ofNat] using unitOfNatDvd (R := R) (d := 4423680) (by decide) hpow
  have hE : IsUnit (52920 : R) := by
    simpa only [Nat.cast_ofNat] using unitOfNatDvd (R := R) (d := 52920) (by decide) hpow
  obtain ⟨d,hd'⟩ := hD
  obtain ⟨e,he'⟩ := hE
  let f := Int.castRingHom R
  let A : Matrix (Fin 10) (Fin 10) R := Matrix.of fun i j => (↑d⁻¹ : R) * f (AInt i j)
  let b : Fin 10 → R := fun i => (↑e⁻¹ : R) * f (bInt i)
  let γ : R := (↑d⁻¹ : R) * 1105920
  have hAu : AInt.map f = f 4423680 • A := by
    ext i j
    simp only [map_ofNat]
    change f (AInt i j) = (4423680 : R) * ((↑d⁻¹ : R) * f (AInt i j))
    rw [←hd', ←mul_assoc]; simp
  have hbu : f ∘ bInt = f 52920 • b := by
    funext i
    simp only [map_ofNat]
    change f (bInt i) = (52920 : R) * ((↑e⁻¹ : R) * f (bInt i))
    rw [←he', ←mul_assoc]; simp
  have hd : IsUnit (f 4423680) := by rw [map_ofNat, ←hd']; exact d.isUnit
  have he : IsUnit (f 52920) := by rw [map_ofNat, ←he']; exact e.isUnit
  have h4 : (4 : R) * γ = 1 := by
    have hdi : (4423680 : R) * (↑d⁻¹ : R) = 1 := by rw [←hd']; simp
    change (4 : R) * ((↑d⁻¹ : R) * 1105920) = 1
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
    let Ω : R := (52920 : R) * (4423680 : R)^7
    have hΩ : IsUnit Ω := by
      simpa only [Ω, map_ofNat] using he.mul (hd.pow 7)
    have hPaid (t : FiniteRootedTree) (ht : (t.order : ℕ) = 8) :
        f ((t.factorial : ℤ) * (bInt ⬝ᵥ Φ t AInt)) = Ω := by
      have hp : (t.factorial : R) * (b ⬝ᵥ Φ t A) = 1 := h8 t (by rw [ht])
      simp only [map_mul, map_natCast, RingHom.map_dotProduct, RKResearch.map_Φ,
        hAu, hbu, Φ_matrix_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, ht, map_ofNat]
      change (t.factorial : R) * ((4423680 : R)^7 *
        ((52920 : R) * (b ⬝ᵥ Φ t A))) = Ω
      linear_combination (norm := ring) Ω * hp
    have hA' := congrArg f numerator_A
    have hB' := congrArg f numerator_B
    rw [map_mul, hPaid treeA orderA] at hA'
    rw [map_mul, hPaid treeB orderB] at hB'
    simp only [map_mul, map_pow, map_ofNat, map_neg] at hA' hB'
    change (576 : R) * Ω = 631 * Ω at hA'
    change (96 : R) * Ω = -5 * Ω at hB'
    exact hΩ.ne_zero (by linear_combination (norm := ring) 11*hA' + 6*hB')

/-- The rational instance has common diagonal one quarter. -/
theorem exists_exact_rational :
    ∃ (A : Matrix (Fin 10) (Fin 10) ℚ) (b : Fin 10 → ℚ),
      A.IsLowerTriangular ∧ (∀ i, A i i = 1/4) ∧
        HasOrder 7 A b ∧ ¬ HasOrder 8 A b := by
  obtain ⟨A,b,γ,ha,hdiag,_,h4,ho,he⟩ :=
    exists_exact (R := ℚ) (isUnit_iff_ne_zero.mpr (by decide +kernel))
  have hγ : γ = (1/4 : ℚ) := mul_left_cancel₀ (by decide : (4:ℚ) ≠ 0)
    (h4.trans (by decide +kernel))
  exact ⟨A,b,ha,fun i => (hdiag i).trans hγ,ho,he⟩

end RKResearch.Certified.SDIRKTenStageOrderSevenPaid

namespace RKResearch
open FiniteRootedTree
open scoped Matrix

/-- Denominator-cleared ordinary order seven already makes 7! a unit. -/
theorem HasOrder.sevenFactorial_isUnit {R : Type*} [CommRing R] [Fintype ι]
    {A : Matrix ι ι R} {b : ι → R} (ho : HasOrder 7 A b) : IsUnit (5040 : R) := by
  apply IsUnit.of_mul_eq_one (b ⬝ᵥ Φ (tallTree 7) A)
  have h := ho (tallTree 7) (by rw [order_tallTree]; decide)
  have hfact : ((tallTree 7).factorial : ℕ) = 5040 := by decide +kernel
  simpa only [hfact, Nat.cast_ofNat] using h

/-- Exact strict order seven is possible at some stage count over
a nonzero commutative ring precisely when 7! is a unit. -/
theorem exists_strictSDIRK_exact_order_seven_iff_factorial_unit {R : Type*}
    [CommRing R] [Nontrivial R] :
    (∃ (s : ℕ) (A : Matrix (Fin s) (Fin s) R) (b : Fin s → R) (γ : R),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ IsUnit γ ∧ HasOrder 7 A b ∧ ¬ HasOrder 8 A b)
      ↔ IsUnit (5040 : R) := by
  constructor
  · rintro ⟨s,A,b,γ,ht,hg,hu,ho,hn⟩
    exact ho.sevenFactorial_isUnit
  · intro h
    obtain ⟨A,b,γ,ht,hg,hu,-,ho,hn⟩ :=
      Certified.SDIRKTenStageOrderSevenPaid.exists_exact h
    exact ⟨10,A,b,γ,ht,hg,hu,ho,hn⟩

end RKResearch
