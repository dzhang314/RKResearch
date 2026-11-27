module

public import RKCert.ReviewedNative.FiniteOrderCheck
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Algebra.QuadraticAlgebra.Basic

@[expose] public section

/-! A six-stage strict tableau of exact order six over the degree-two extension of F₃₅₃₃.
The diagonal already lies in the prime subfield. -/
namespace RKResearch.Certified.SDIRKSix3533Quadratic

open FiniteRootedTree
open scoped Matrix

abbrev F := ZMod 3533
abbrev E := QuadraticAlgebra F (3009 : F) (824 : F)

set_option maxRecDepth 16384 in
instance prime : Fact (Nat.Prime 3533) := ⟨by decide +kernel⟩

private theorem noRootCodes : ∀ i : Fin 59, ∀ j : Fin 60,
    let r : F := (((i.val * 60 + j.val : ℕ)) : F)
    r ^ 2 ≠ 3009 + 824 * r := by
  decide +kernel

instance noRoot : Fact (∀ r : F, r ^ 2 ≠ 3009 + 824 * r) := by
  constructor
  intro r
  let i : Fin 59 := ⟨r.val / 60, by have := r.val_lt; omega⟩
  let j : Fin 60 := ⟨r.val % 60, Nat.mod_lt _ (by decide)⟩
  have code : i.val * 60 + j.val = r.val := by
    dsimp only [i, j]
    omega
  have h := noRootCodes i j
  change (((i.val * 60 + j.val : ℕ) : F)) ^ 2 ≠ 3009 + 824 * (((i.val * 60 + j.val : ℕ) : F)) at h
  simpa only [code, ZMod.natCast_zmod_val] using h

noncomputable example : Field E := inferInstance

theorem extension_degree : Module.finrank F E = 2 := QuadraticAlgebra.finrank_eq_two _ _

def gamma : E := ⟨189, 0⟩

def A : Matrix (Fin 6) (Fin 6) E := Matrix.of fun i j =>
  if i = j then gamma else
    match i.val, j.val with
    | 1, 0 => ⟨0, 189⟩
    | 2, 0 => ⟨2745, 1843⟩
    | 2, 1 => ⟨788, 2068⟩
    | 3, 0 => ⟨2173, 3495⟩
    | 3, 1 => ⟨1879, 1007⟩
    | 3, 2 => ⟨2069, 2942⟩
    | 4, 0 => ⟨1887, 1429⟩
    | 4, 1 => ⟨3333, 1435⟩
    | 4, 2 => ⟨402, 3451⟩
    | 4, 3 => ⟨783, 940⟩
    | 5, 0 => ⟨1819, 1427⟩
    | 5, 1 => ⟨3451, 450⟩
    | 5, 2 => ⟨1379, 519⟩
    | 5, 3 => ⟨3235, 628⟩
    | 5, 4 => ⟨338, 509⟩
    | _, _ => 0

def b (i : Fin 6) : E :=
  match i.val with
  | 0 => ⟨3051, 55⟩
  | 1 => ⟨1199, 318⟩
  | 2 => ⟨974, 176⟩
  | 3 => ⟨1145, 3357⟩
  | 4 => ⟨1789, 3215⟩
  | _ => ⟨2442, 3478⟩

def c (i : Fin 6) : E :=
  match i.val with
  | 0 => ⟨189, 0⟩
  | 1 => ⟨189, 189⟩
  | 2 => ⟨189, 378⟩
  | 3 => ⟨2777, 378⟩
  | 4 => ⟨3061, 189⟩
  | _ => ⟨3345, 0⟩

theorem lowerTriangular : A.IsLowerTriangular := by
  change ∀ i j : Fin 6, i < j → A i j = 0
  simp only [A, Matrix.of_apply]
  decide +kernel

theorem diagonal (i : Fin 6) : A i i = gamma := by simp [A]

theorem diagonal_ne_zero : gamma ≠ 0 := by decide +kernel

theorem weights_ne_zero : ∀ i : Fin 6, b i ≠ 0 := by decide +kernel

theorem row_sums : A *ᵥ 1 = c := by
  funext i
  exact (by decide +kernel : ∀ i : Fin 6, (A *ᵥ 1) i = c i) i

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
theorem order_six : HasOrder 6 A b := by
  apply (checkOrder_iff A b 6).mp
  decide +kernel

theorem seventh_bush_value :
    ((bushyTree 7).factorial : E) * (b ⬝ᵥ Φ (bushyTree 7) A) = ⟨1230, 0⟩ := by
  rw [factorial_bushyTree, Φ_bushyTree, row_sums]
  decide +kernel

theorem not_order_seven : ¬ HasOrder 7 A b := by
  intro h
  have hp := h (bushyTree 7) (by rw [order_bushyTree]; decide)
  rw [seventh_bush_value] at hp
  exact (by decide +kernel : (⟨1230, 0⟩ : E) ≠ 1) hp

theorem exists_exact :
    ∃ (M : Matrix (Fin 6) (Fin 6) E) (w : Fin 6 → E) (γ : E),
      M.IsLowerTriangular ∧ (∀ i, M i i = γ) ∧ γ ≠ 0 ∧
      HasOrder 6 M w ∧ ¬ HasOrder 7 M w :=
  ⟨A, b, gamma, lowerTriangular, diagonal, diagonal_ne_zero, order_six, not_order_seven⟩

/-- The explicit witness transfers to every characteristic-3533 coefficient field
containing a square root of 2077; this condition is also forced by the
independent scalar-chart lower bound. -/
theorem exists_exact_of_sqrt {K : Type*} [Field K] [CharP K 3533]
    (hx : ∃ x : K, x ^ 2 = 2077) :
    ∃ (M : Matrix (Fin 6) (Fin 6) K) (w : Fin 6 → K) (γ : K),
      M.IsLowerTriangular ∧ (∀ i, M i i = γ) ∧ γ ≠ 0 ∧
      HasOrder 6 M w ∧ ¬ HasOrder 7 M w := by
  obtain ⟨x,hx⟩ := hx
  have hchar : (3533 : K) = 0 := CharP.cast_eq_zero K 3533
  have hsmall {n : ℕ} (h : ¬ 3533 ∣ n) : (n : K) ≠ 0 :=
    fun e => h ((CharP.cast_eq_zero_iff K 3533 n).mp e)
  have h2 : (2 : K) ≠ 0 := hsmall (n := 2) (by decide)
  have h4 : (4 : K) ≠ 0 := hsmall (n := 4) (by decide)
  let t : K := (x+824)/2
  have ht : 2*t = x+824 := by dsimp [t]; field_simp
  letI : Algebra F K := (ZMod.castHom (m := 3533) (n := 3533) dvd_rfl K).toAlgebra
  have hh : t*t = (3009 : F) • (1:K) + (824 : F) • t := by
    simp only [Algebra.smul_def, map_ofNat, mul_one]
    apply mul_left_cancel₀ h4
    linear_combination (norm := ring) (2*t+x-824)*ht + hx - 195*hchar
  let f : E →+* K := (QuadraticAlgebra.lift ⟨t,hh⟩).toRingHom
  refine ⟨A.map f, f ∘ b, f gamma, ?_, ?_, ?_, order_six.map f, ?_⟩
  · intro i j hij
    change f (A i j) = 0
    rw [lowerTriangular hij, map_zero]
  · intro i
    change f (A i i) = f gamma
    rw [diagonal]
  · exact fun e => diagonal_ne_zero (f.injective (e.trans f.map_zero.symm))
  · exact fun h => not_order_seven ((hasOrder_map_iff f.injective).mp h)

end RKResearch.Certified.SDIRKSix3533Quadratic
