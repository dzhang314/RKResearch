module

public import RKCert.ReviewedNative.NativePencilProjectionLift
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

/-! # Uniform elimination from literal residue Bezout witnesses

The residue field is chosen algebraically closed. No physical parameter is
mapped down to it: all resultants are formed on literal integer polynomials
before specialization. In particular neither t nor x needs a chosen lift. -/
namespace RKResearch.Certified.Graded.NativePencilProjection
open Polynomial
noncomputable section

private theorem coprime_of_eval_ne_zero_or
    {k : Type*} [Field k] [IsAlgClosed k] (A B : k[X])
    (h : ∀ x : k, A.eval x ≠ 0 ∨ B.eval x ≠ 0) : IsCoprime A B := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed k k A B).mpr
  intro x
  simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using h x

private theorem resultant_nonzero_of_full_left
    {k : Type*} [Field k] [IsAlgClosed k] (A B : k[X]) (m n : ℕ)
    (am : A.natDegree ≤ m) (bn : B.natDegree ≤ n) (full : A.coeff m ≠ 0)
    (roots : ∀ t : k, A.eval t = 0 → B.eval t ≠ 0) : A.resultant B m n ≠ 0 := by
  have exactA : A.natDegree = m := natDegree_eq_of_le_of_coeff_ne_zero am full
  have cop : IsCoprime A B := by
    apply coprime_of_eval_ne_zero_or A B
    intro t
    by_cases ha : A.eval t = 0
    · exact Or.inr (roots t ha)
    · exact Or.inl ha
  have pad : A.resultant B m n = A.coeff m ^ (n-B.natDegree) * A.resultant B := by
    calc
      A.resultant B m n = A.resultant B m (B.natDegree+(n-B.natDegree)) := by
        rw [Nat.add_sub_of_le bn]
      _ = A.coeff m ^ (n-B.natDegree) * A.resultant B m B.natDegree :=
        resultant_add_right_deg A B m B.natDegree (n-B.natDegree) le_rfl
      _ = _ := by rw [exactA]
  rw [pad]
  exact mul_ne_zero (pow_ne_zero _ full) (resultant_ne_zero A B cop)

/-- It suffices to rule out the two scalar equations in the algebraically
closed residue field, provided the first t-leading term survives there. -/
theorem residue_projection_coprime
    {k : Type*} [Field k] [IsAlgClosed k] (r : ZPoly) (A B : TPoly)
    (m n : ℕ) (am : A.natDegree≤m) (bn : B.natDegree≤n)
    (hyp : ∀ z : k, zEval z r=0 →
      zEval z (A.coeff m) ≠ 0 ∧ ∀ t : k, tEval z t A=0 → tEval z t B≠0) :
    IsCoprime (r.map (Int.castRingHom k)) ((A.resultant B m n).map (Int.castRingHom k)) := by
  apply coprime_of_eval_ne_zero_or
  intro z
  simp only [Polynomial.eval_map]
  change zEval z r ≠ 0 ∨ zEval z (A.resultant B m n) ≠ 0
  by_cases hz : zEval z r=0
  · right
    obtain ⟨full,gate⟩ := hyp z hz
    let φ : ZPoly →+* k := zEval z
    have degreeA : (A.map φ).natDegree ≤ m := natDegree_map_le.trans am
    have degreeB : (B.map φ).natDegree ≤ n := natDegree_map_le.trans bn
    have leadingA : (A.map φ).coeff m ≠ 0 := by
      rw [coeff_map]
      exact full
    change φ (A.resultant B m n) ≠ 0
    rw [← resultant_map_map A B m n φ]
    apply resultant_nonzero_of_full_left (A.map φ) (B.map φ) m n degreeA degreeB leadingA
    intro t ht
    have left : tEval z t A = 0 := by
      change A.eval₂ φ t = 0
      simpa only [Polynomial.eval_map] using ht
    have right : tEval z t B ≠ 0 := gate t left
    rw [Polynomial.eval_map]
    exact right
  · exact Or.inl hz

/-- Nested finite gate: full t-degree for A and full x-degree for P suffice.
There is no required leading coefficient for H or either resultant. -/
theorem residue_nested_projection_coprime
    {k : Type*} [Field k] [IsAlgClosed k] (r : ZPoly) (A : TPoly) (H P : XPoly)
    (m v : ℕ) (am : A.natDegree≤m) (pv : P.natDegree≤v)
    (hyp : ∀ z : k, zEval z r=0 → zEval z (A.coeff m)≠0 ∧
      ∀ t : k, tEval z t A=0 → tEval z t (P.coeff v)≠0 ∧
        ∀ x : k, P.eval₂ (tEval z t) x=0 → H.eval₂ (tEval z t) x≠0) :
    IsCoprime (r.map (Int.castRingHom k))
      ((A.resultant (H.resultant P H.natDegree v) m
        (H.resultant P H.natDegree v).natDegree).map (Int.castRingHom k)) := by
  let D : TPoly := H.resultant P H.natDegree v
  change IsCoprime (r.map (Int.castRingHom k))
    ((A.resultant D m D.natDegree).map (Int.castRingHom k))
  apply residue_projection_coprime r A D m D.natDegree am le_rfl
  intro z hz
  obtain ⟨ha,gate⟩ := hyp z hz
  refine ⟨ha,?_⟩
  intro t ht
  obtain ⟨pfull,root⟩ := gate t ht
  let φ : TPoly →+* k := tEval z t
  have degreeP : (P.map φ).natDegree ≤ v := natDegree_map_le.trans pv
  have degreeH : (H.map φ).natDegree ≤ H.natDegree := natDegree_map_le
  have leadingP : (P.map φ).coeff v ≠ 0 := by
    rw [coeff_map]
    exact pfull
  have reverseNZ : (P.map φ).resultant (H.map φ) v H.natDegree ≠ 0 := by
    apply resultant_nonzero_of_full_left (P.map φ) (H.map φ) v H.natDegree
      degreeP degreeH leadingP
    intro x hx
    simp only [Polynomial.eval_map] at hx ⊢
    exact root x hx
  change φ (H.resultant P H.natDegree v) ≠ 0
  rw [← resultant_map_map H P H.natDegree v φ,
    resultant_comm (H.map φ) (P.map φ) H.natDegree v]
  have signNZ : (-1 : k) ^ (H.natDegree * v) ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  exact mul_ne_zero signNZ reverseNZ

end
end RKResearch.Certified.Graded.NativePencilProjection
