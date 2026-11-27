module

public import RKCert.ReviewedNative.FiniteOrderCheck
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.FinCases

@[expose] public section

/-! Literal nine-stage exact order-seven certificates modulo 19² and 19¹².
In particular, the top witness works by base change in every nontrivial
commutative ring where 19¹² vanishes. -/

namespace RKResearch.Certified.SDIRKNineStageOrderSeven19Powers

open FiniteRootedTree
open scoped Matrix

namespace Pow2

abbrev F := ZMod 361

def gamma : F := 293

def A : Matrix (Fin 9) (Fin 9) F :=
  !![293,0,0,0,0,0,0,0,0;
     131,293,0,0,0,0,0,0,0;
     137,216,293,0,0,0,0,0,0;
     290,295,93,293,0,0,0,0,0;
     65,211,218,204,293,0,0,0,0;
     329,95,172,147,18,293,0,0,0;
     14,55,210,272,33,83,293,0,0;
     12,68,136,177,289,83,359,293,0;
     286,226,2,5,171,25,72,72,293]

def b : Fin 9 → F := ![0,0,0,250,70,281,193,279,11]
def c : Fin 9 → F := ![293,63,285,249,269,332,238,334,69]

theorem lowerTriangular : A.IsLowerTriangular := by
  intro i j h
  change i.val < j.val at h
  fin_cases i <;> fin_cases j <;> first | (norm_num at h; done) | decide +kernel

theorem diagonal : ∀ i : Fin 9, A i i = gamma := by decide +kernel

theorem gamma_isUnit : IsUnit gamma :=
  IsUnit.of_mul_eq_one _ (by decide +kernel : gamma * 69 = 1)

theorem row_sums : A *ᵥ 1 = c := by
  funext i
  exact (by decide +kernel : ∀ i : Fin 9, (A *ᵥ 1) i = c i) i

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 20000 in
theorem order_seven : HasOrder 7 A b := by
  apply (checkOrder_iff A b 7).mp
  decide +kernel

theorem eighth_bush_value :
    ((bushyTree 8).factorial : F) * (b ⬝ᵥ Φ (bushyTree 8) A) = 278 := by
  rw [factorial_bushyTree, Φ_bushyTree, row_sums]
  decide +kernel

/-- Both order and strictness survive every nontrivial ring base change.
The eighth-order defect itself, not just the diagonal, is a unit. -/
theorem exists_exact_map {R : Type*} [CommRing R] [Nontrivial R] (f : F →+* R) :
    ∃ (M : Matrix (Fin 9) (Fin 9) R) (w : Fin 9 → R) (γ : R),
      M.IsLowerTriangular ∧ (∀ i, M i i = γ) ∧ IsUnit γ ∧
      HasOrder 7 M w ∧ ¬ HasOrder 8 M w := by
  refine ⟨A.map f, f ∘ b, f gamma, lowerTriangular.map f,
    fun i => congrArg f (diagonal i), gamma_isUnit.map f, order_seven.map f, ?_⟩
  intro h
  have e := h (bushyTree 8) (by rw [order_bushyTree]; decide)
  have eqv := congrArg f eighth_bush_value
  simp only [map_mul, map_natCast, RingHom.map_dotProduct, RKResearch.map_Φ] at eqv
  have en : f (278 : F) = 1 := eqv.symm.trans e
  have uf : IsUnit ((278 : F) - 1) :=
    IsUnit.of_mul_eq_one _ (by decide +kernel : ((278 : F) - 1) * 159 = 1)
  have nz := (uf.map f).ne_zero
  exact nz (by rw [map_sub, map_one, en, sub_self])

theorem exists_exact :
    ∃ (M : Matrix (Fin 9) (Fin 9) F) (w : Fin 9 → F) (γ : F),
      M.IsLowerTriangular ∧ (∀ i, M i i = γ) ∧ IsUnit γ ∧
      HasOrder 7 M w ∧ ¬ HasOrder 8 M w := by
  let : Fact (1 < 361) := ⟨by decide +kernel⟩
  exact exists_exact_map (RingHom.id F)

end Pow2

namespace Pow12

abbrev F := ZMod 2213314919066161

def gamma : F := 1310024100145885

def A : Matrix (Fin 9) (Fin 9) F :=
  !![1310024100145885,0,0,0,0,0,0,0,0;
     912296118460107,1310024100145885,0,0,0,0,0,0,0;
     1665409045487260,1570385952844703,1310024100145885,0,0,0,0,0,0;
     1290057796541769,582601332651843,1939358010506361,1310024100145885,0,0,0,0,0;
     1366542989912933,384864437647408,1807582540052378,1647693777425212,1310024100145885,0,0,0,0;
     544033743953961,170548071999744,1270687814966474,1289755232116304,1169051113420936,1310024100145885,0,0,0;
     1791015150124162,1094463199295564,316543912863991,1142930259530244,89895588002387,931101269489325,1310024100145885,0,0;
     632107540800542,214362172031506,642036649132559,1649584076584184,1996954304128726,1542838901747322,1335011702280596,1310024100145885,0;
     68223425762103,5271692086596,2,5,93877415370113,669248054145229,545294805787140,424666244689365,1310024100145885]

def b : Fin 9 → F := ![0,0,0,461711843460801,1096131043944298,335676994052601,445055737464330,2088054219210282,11]
def c : Fin 9 → F := ![1310024100145885,9005299539831,119189260345526,695411401713536,2090078007051494,1327470238470982,36028722253075,469659770586676,903290818920277]

theorem lowerTriangular : A.IsLowerTriangular := by
  intro i j h
  change i.val < j.val at h
  fin_cases i <;> fin_cases j <;> first | (norm_num at h; done) | decide +kernel

theorem diagonal : ∀ i : Fin 9, A i i = gamma := by decide +kernel

theorem gamma_isUnit : IsUnit gamma :=
  IsUnit.of_mul_eq_one _ (by decide +kernel : gamma * 745775781599446 = 1)

theorem row_sums : A *ᵥ 1 = c := by
  funext i
  exact (by decide +kernel : ∀ i : Fin 9, (A *ᵥ 1) i = c i) i

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 20000 in
theorem order_seven : HasOrder 7 A b := by
  apply (checkOrder_iff A b 7).mp
  decide +kernel

theorem eighth_bush_value :
    ((bushyTree 8).factorial : F) * (b ⬝ᵥ Φ (bushyTree 8) A) = 1281827714603969 := by
  rw [factorial_bushyTree, Φ_bushyTree, row_sums]
  decide +kernel

/-- Both order and strictness survive every nontrivial ring base change.
The eighth-order defect itself, not just the diagonal, is a unit. -/
theorem exists_exact_map {R : Type*} [CommRing R] [Nontrivial R] (f : F →+* R) :
    ∃ (M : Matrix (Fin 9) (Fin 9) R) (w : Fin 9 → R) (γ : R),
      M.IsLowerTriangular ∧ (∀ i, M i i = γ) ∧ IsUnit γ ∧
      HasOrder 7 M w ∧ ¬ HasOrder 8 M w := by
  refine ⟨A.map f, f ∘ b, f gamma, lowerTriangular.map f,
    fun i => congrArg f (diagonal i), gamma_isUnit.map f, order_seven.map f, ?_⟩
  intro h
  have e := h (bushyTree 8) (by rw [order_bushyTree]; decide)
  have eqv := congrArg f eighth_bush_value
  simp only [map_mul, map_natCast, RingHom.map_dotProduct, RKResearch.map_Φ] at eqv
  have en : f (1281827714603969 : F) = 1 := eqv.symm.trans e
  have uf : IsUnit ((1281827714603969 : F) - 1) :=
    IsUnit.of_mul_eq_one _ (by decide +kernel : ((1281827714603969 : F) - 1) * 571760746997084 = 1)
  have nz := (uf.map f).ne_zero
  exact nz (by rw [map_sub, map_one, en, sub_self])

theorem exists_exact :
    ∃ (M : Matrix (Fin 9) (Fin 9) F) (w : Fin 9 → F) (γ : F),
      M.IsLowerTriangular ∧ (∀ i, M i i = γ) ∧ IsUnit γ ∧
      HasOrder 7 M w ∧ ¬ HasOrder 8 M w := by
  let : Fact (1 < 2213314919066161) := ⟨by decide +kernel⟩
  exact exists_exact_map (RingHom.id F)

end Pow12

/-- If 19¹² vanishes in the coefficient ring, nine strict singly
diagonally implicit stages suffice for exact order seven. This does not
assume a field or lift to characteristic zero. -/
theorem exists_exact_of_pow_eq_zero (R : Type*) [CommRing R] [Nontrivial R]
    (h : (19 : R) ^ (12 : ℕ) = 0) :
    ∃ (M : Matrix (Fin 9) (Fin 9) R) (w : Fin 9 → R) (γ : R),
      M.IsLowerTriangular ∧ (∀ i, M i i = γ) ∧ IsUnit γ ∧
      HasOrder 7 M w ∧ ¬ HasOrder 8 M w := by
  have h' : ((2213314919066161 : ℕ) : R) = 0 := by
    rw [show (2213314919066161 : ℕ) = (19 : ℕ) ^ 12 by decide +kernel, Nat.cast_pow]
    simpa only [Nat.cast_ofNat] using h
  exact Pow12.exists_exact_map (ZMod.castHom (ringChar.dvd h') R)

end RKResearch.Certified.SDIRKNineStageOrderSeven19Powers
