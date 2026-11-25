module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.NormNum

@[expose] public section

/-! # One sound residue place for distinct monic roots

The original field need not be a number field. Algebraic integrality comes
from the literal monic integer equation. A single prime residue map is used
for both roots. Separability of the reduced polynomial, not injectivity of
the residue map, preserves their distinctness. -/

namespace RKResearch.Certified.Graded.NativeModularRootLift

open Polynomial
universe u

noncomputable section

private theorem prime_not_unit_in_integralClosure (E : Type u) [Field E] [CharZero E]
    (p : ℕ) (pp : p.Prime) : ¬ IsUnit (p : integralClosure ℤ E) := by
  intro unit
  let B := integralClosure ℤ E
  obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.mp unit
  have ez : (p : E) * (z : E) = 1 := by
    have h := congrArg (algebraMap B E) hz
    simpa only [map_mul, map_natCast, map_one, Subalgebra.algebraMap_apply] using h
  have p0 : (p : E) ≠ 0 := Nat.cast_ne_zero.mpr pp.ne_zero
  have zr : (z : E) ∈ Set.range (Rat.cast : ℚ → E) := by
    refine ⟨((p : ℚ)⁻¹), ?_⟩
    rw [Rat.cast_inv, Rat.cast_natCast]
    apply mul_left_cancel₀ p0
    rw [mul_inv_cancel₀ p0, ez]
  have zi : IsIntegral ℤ (z : E) := z.2
  obtain ⟨r, hr⟩ := zi.mem_range_ratCast_iff.mp zr
  have int : (p : ℤ) * r = 1 := by
    apply (Int.cast_injective : Function.Injective (fun i : ℤ => (i : E)))
    simp only [Int.cast_mul, Int.cast_natCast, Int.cast_one]
    rw [hr]
    exact ez
  have dz : (p : ℤ) ∣ (1 : ℤ) := ⟨r, int.symm⟩
  have dn : p ∣ 1 := Int.natCast_dvd_natCast.mp (by simpa using dz)
  exact (not_le_of_gt pp.one_lt) (Nat.le_of_dvd (by decide) dn)

/-- Eliminator for a single field above the prime, requiring no splitting
field or finite extension of the original characteristic-zero field. -/
theorem with_integral_reduction (E : Type u) [Field E] [CharZero E]
    (p : ℕ) (pp : p.Prime) {goal : Prop}
    (h : ∀ (k : Type u) [Field k] [CharP k p], (integralClosure ℤ E →+* k) → goal) :
    goal := by
  classical
  let B := integralClosure ℤ E
  let I : Ideal B := Ideal.span {(p:B)}
  have proper : I ≠ ⊤ := fun top =>
    prime_not_unit_in_integralClosure E p pp (Ideal.span_singleton_eq_top.mp top)
  obtain ⟨m, hm, inc⟩ := Ideal.exists_le_maximal I proper
  letI : m.IsMaximal := hm
  let k := B ⧸ m
  letI : Field k := Ideal.Quotient.field m
  let q : B →+* k := Ideal.Quotient.mk m
  have eq : (p : k) = 0 := by
    have hp : (p : B) ∈ m := inc (Ideal.subset_span (by simp [I]))
    have e : q (p : B) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
    simpa only [map_natCast] using e
  letI : CharP k p := (CharP.charP_iff_prime_eq_zero pp).mpr eq
  exact h k q

/-- Distinct roots in a domain have distinct images whenever the target
polynomial is separable. This is not a claim that the ring map is one-to-one. -/
theorem distinct_reductions_of_separable
    {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [Nontrivial S]
    (q : R →+* S) {P : R[X]} (separable : (P.map q).Separable)
    {a b : R} (ha : P.IsRoot a) (hb : P.IsRoot b) (different : a ≠ b) :
    q a ≠ q b := by
  intro same
  obtain ⟨G, hG⟩ := (dvd_iff_isRoot (a:=a)).mpr ha
  have hbG : G.IsRoot b := by
    have e := hb.eq_zero
    rw [hG, eval_mul, eval_sub, eval_X, eval_C] at e
    exact (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr different.symm)
  obtain ⟨H, hH⟩ := (dvd_iff_isRoot (a:=b)).mpr hbG
  have square : (X - C (q a)) * (X - C (q a)) ∣ P.map q := by
    refine ⟨H.map q, ?_⟩
    rw [hG, hH, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_sub,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.map_C, same, mul_assoc]
  exact not_isUnit_X_sub_C _ (isUnit_of_self_mul_dvd_separable separable square)

/-- A monic integer root gives a point of the integral closure. -/
theorem integral_of_monic_int_root {E : Type u} [Field E] [CharZero E]
    {P : ℤ[X]} (monic : P.Monic) {a : E}
    (root : (P.map (algebraMap ℤ E)).IsRoot a) : IsIntegral ℤ a := by
  refine ⟨P, monic, ?_⟩
  change aeval a P = 0
  rw [← eval_map_algebraMap P a]
  exact root.eq_zero

/-- Two literal characteristic-zero roots of a monic integral polynomial
specialize together to distinct roots of the same residue polynomial.
The residue field may be an extension of ZMod p. -/
theorem with_distinct_monic_root_reduction
    {E : Type u} [Field E] [CharZero E] (p : ℕ) (pp : p.Prime)
    {P : ℤ[X]} (monic : P.Monic)
    (separable : (P.map (Int.castRingHom (ZMod p))).Separable)
    {a b : E} (ha : (P.map (algebraMap ℤ E)).IsRoot a)
    (hb : (P.map (algebraMap ℤ E)).IsRoot b) (different : a ≠ b) {goal : Prop}
    (h : ∀ (k : Type u) [Field k] [CharP k p]
       (q : integralClosure ℤ E →+* k) (A B : integralClosure ℤ E),
       (A : E) = a → (B : E) = b →
       (P.map (Int.castRingHom k)).IsRoot (q A) →
       (P.map (Int.castRingHom k)).IsRoot (q B) → q A ≠ q B → goal) : goal := by
  classical
  let C := integralClosure ℤ E
  let e : C →+* E := algebraMap C E
  have inj : Function.Injective e := fun _ _ z => Subtype.ext z
  let P₀ := P.map (algebraMap ℤ C)
  have mapped : P₀.map e = P.map (algebraMap ℤ E) := by
    dsimp only [P₀,e]
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq ℤ C E]
  let A : C := ⟨a, integral_of_monic_int_root monic ha⟩
  let B : C := ⟨b, integral_of_monic_int_root monic hb⟩
  have lift {x : C} (hr : (P.map (algebraMap ℤ E)).IsRoot (e x)) :
      P₀.IsRoot x := by
    change P₀.eval x = 0
    apply inj
    rw [← eval_map_apply, mapped, hr.eq_zero, map_zero]
  have hA : P₀.IsRoot A := lift ha
  have hB : P₀.IsRoot B := lift hb
  have neq : A ≠ B := fun r => different (congrArg e r)
  refine with_integral_reduction E p pp ?_
  intro k _ _ q
  let z := ZMod.castHom (dvd_refl p) k
  have red : P₀.map q = P.map (Int.castRingHom k) := by
    dsimp only [P₀]
    rw [Polynomial.map_map]
    exact congrArg (fun f : ℤ →+* k => P.map f) (RingHom.ext_int _ _)
  have refactor : P.map (Int.castRingHom k) = (P.map (Int.castRingHom (ZMod p))).map z := by
    rw [Polynomial.map_map]
    exact congrArg (fun f : ℤ →+* k => P.map f) (RingHom.ext_int _ _)
  have s : (P₀.map q).Separable := by
    rw [red, refactor]
    exact separable.map
  exact h k q A B rfl rfl (red ▸ hA.map q) (red ▸ hB.map q)
    (distinct_reductions_of_separable q s hA hB neq)

end
end RKResearch.Certified.Graded.NativeModularRootLift
