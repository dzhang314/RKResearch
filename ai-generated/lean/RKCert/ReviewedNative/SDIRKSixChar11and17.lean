module

public import RKCert.ReviewedNative.FiniteOrderCheck
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

/-!
# Six-stage strict SDIRK order six in characteristics 11 and 17

One CRT tableau over Z/(11*17) suffices. Both its diagonal and its seventh
bush discrepancy are units; hence *every* nontrivial commutative target
ring of characteristic dividing 187 inherits exact order six.
-/
namespace RKResearch.Certified.SDIRKSixChar11and17

open FiniteRootedTree
open scoped Matrix

abbrev S := ZMod 187
def gamma : S := 59
def A : Matrix (Fin 6) (Fin 6) S := Matrix.of fun i j =>
  if i = j then gamma else
    match i.val, j.val with
    | 1, 0 => 148
    | 2, 0 => 4
    | 2, 1 => 105
    | 3, 0 => 26
    | 3, 1 => 64
    | 3, 2 => 97
    | 4, 0 => 40
    | 4, 1 => 46
    | 4, 2 => 145
    | 4, 3 => 178
    | 5, 0 => 97
    | 5, 1 => 12
    | 5, 2 => 45
    | 5, 3 => 47
    | 5, 4 => 56
    | _, _ => 0

def b (i : Fin 6) : S :=
  match i.val with
  | 3 | 5 => 73
  | 4 => 42
  | _ => 0

theorem lowerTriangular : A.IsLowerTriangular := by
  change ∀ i j : Fin 6, i < j → A i j = 0
  simp only [A, Matrix.of_apply]
  decide +kernel

theorem diagonal (i : Fin 6) : A i i = gamma := by simp [A]

theorem gamma_unit : IsUnit gamma :=
  IsUnit.of_mul_eq_one _ (by decide +kernel : gamma * 168 = 1)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
theorem order_six : HasOrder 6 A b := by
  apply (checkOrder_iff A b 6).mp
  decide +kernel

theorem seventh_bush_value :
    ((bushyTree 7).factorial : S) * (b ⬝ᵥ Φ (bushyTree 7) A) = 152 := by
  rw [factorial_bushyTree, Φ_bushyTree]
  decide +kernel

private theorem discrepancy_unit : IsUnit ((152 : S) - 1) :=
  IsUnit.of_mul_eq_one _ (by decide +kernel : ((152 : S) - 1) * 161 = 1)

/-- No reducedness, integral-domain or algebraic-closure assumption. -/
theorem exact_map {R : Type*} [CommRing R] [Nontrivial R] (f : S →+* R) :
    (A.map f).IsLowerTriangular ∧ (∀ i, (A.map f) i i = f gamma) ∧
    IsUnit (f gamma) ∧ HasOrder 6 (A.map f) (f ∘ b) ∧
    ¬ HasOrder 7 (A.map f) (f ∘ b) := by
  refine ⟨lowerTriangular.map f, fun i => congrArg f (diagonal i),
    gamma_unit.map f, order_six.map f, ?_⟩
  intro h
  have hp := h (bushyTree 7) (by rw [order_bushyTree]; decide)
  have hv := congrArg f seventh_bush_value
  simp only [map_mul, map_natCast, RingHom.map_dotProduct, map_Φ] at hv
  have he : f 152 = 1 := hv.symm.trans hp
  exact (discrepancy_unit.map f).ne_zero (by rw [map_sub, map_one, he, sub_self])

/-- In particular use m=11, 17, or 187. The nonzero unit common diagonal
is strict, even when the target ring has zero divisors or nilpotents. -/
theorem exists_exact_of_char_dvd {R : Type*} [CommRing R] [Nontrivial R]
    {m : ℕ} [CharP R m] (hm : m ∣ 187) :
    ∃ (T : Matrix (Fin 6) (Fin 6) R) (w : Fin 6 → R) (d : R),
      T.IsLowerTriangular ∧ (∀ i, T i i = d) ∧ IsUnit d ∧
      HasOrder 6 T w ∧ ¬ HasOrder 7 T w := by
  let f := ZMod.castHom hm R
  exact ⟨A.map f, f ∘ b, f gamma, exact_map f⟩

end RKResearch.Certified.SDIRKSixChar11and17
