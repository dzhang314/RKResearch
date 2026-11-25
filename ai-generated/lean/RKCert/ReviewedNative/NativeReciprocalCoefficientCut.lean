module

public import RKCert.ReviewedNative.NativeReciprocalPrimitive
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKResearch.Certified.Graded.NativeReciprocal

open Polynomial
open scoped BigOperators

noncomputable section

private def coefficientSum {B : Type*} [CommRing B] {d : ℕ}
    (rate : Fin (d + 1) → ℤ) (P : B[X]) (t : B) : B :=
  ∑ i : Fin (d + 1), (rate i : B) * P.coeff (d - i.val) * t ^ (d - i.val)

private theorem map_coefficientSum {B D : Type*} [CommRing B] [CommRing D] {d : ℕ}
    (f : B →+* D) (rate : Fin (d + 1) → ℤ) (P : B[X]) (t : B) :
    f (coefficientSum rate P t) = coefficientSum rate (P.map f) (f t) := by
  simp only [coefficientSum, map_sum, map_mul, map_pow, map_intCast, coeff_map]

private theorem primitive_eval_pow {E : Type*} [Field E] {P : E[X]} {d : ℕ}
    (pd : P.natDegree ≤ d) (ν : ℕ) (x : E) :
    (primitive (X^ν * P)).eval x =
      ∑ i : Fin (d + 1), P.coeff i.val / ((i.val + ν + 1 : ℕ) : E) *
        x ^ (i.val + ν + 1) := by
  classical
  let c := toFn (d + 1) P
  have rep : ofFn (d + 1) c = P :=
    ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_of_le pd)
  conv_lhs => rw [← rep, ofFn_eq_sum_monomial, Finset.mul_sum, map_sum, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  change (primitive (X^ν * monomial i.val (P.coeff i.val))).eval x = _
  rw [X_pow_mul_monomial, primitive_monomial, eval_monomial]

private theorem coefficientSum_of_primitive_zero {E : Type*} [Field E] [CharZero E]
    {d : ℕ} (ν : ℕ) (L : ℤ) (rate : Fin (d + 1) → ℤ)
    (paid : ∀ i : Fin (d + 1), rate i * ((i.val + ν + 1 : ℕ) : ℤ) = L)
    {P : E[X]} (pd : P.natDegree = d) (p0 : P.coeff 0 ≠ 0)
    {a t : E} (a0 : a ≠ 0) (t0 : t ≠ 0)
    (zero : (primitive (X^ν * P)).eval (a / t) = 0) :
    coefficientSum rate (scaledReciprocal P a) t = 0 := by
  let m : E := (L : E) * (P.coeff 0)⁻¹ * t^(d + ν + 1) / a^(ν + 1)
  have ident : coefficientSum rate (scaledReciprocal P a) t =
      m * (primitive (X^ν * P)).eval (a / t) := by
    rw [primitive_eval_pow pd.le, coefficientSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have id : i.val ≤ d := Nat.lt_succ_iff.mp i.isLt
    have deg : d - i.val ≤ P.natDegree := by rw [pd]; exact Nat.sub_le _ _
    have idx : d - (d - i.val) = i.val := by omega
    rw [scaledReciprocal_coeff p0 a deg, pd, idx]
    have dn : ((i.val + ν + 1 : ℕ) : E) ≠ 0 :=
      Nat.cast_ne_zero.mpr (by omega)
    have divRate : (rate i : E) = (L : E) / ((i.val + ν + 1 : ℕ) : E) := by
      apply (eq_div_iff dn).mpr
      simpa only [Int.cast_mul, Int.cast_natCast] using
        congrArg (fun z : ℤ => (z : E)) (paid i)
    have tx : t^(d + ν + 1) = t^(d - i.val) * t^(i.val + ν + 1) := by
      rw [← pow_add, show d - i.val + (i.val + ν + 1) = d + ν + 1 by omega]
    have ax : a^(i.val + ν + 1) = a^i.val * a^(ν + 1) := by
      rw [← pow_add, Nat.add_assoc]
    have at0 : a^(ν + 1) ≠ 0 := pow_ne_zero _ a0
    have tt0 : t^(i.val + ν + 1) ≠ 0 := pow_ne_zero _ t0
    dsimp only [m]
    rw [divRate, div_pow, tx, ax]
    field_simp [dn, at0, tt0, a0, t0, p0] <;> ring
  rw [ident, zero, mul_zero]

/-- A nonzero coefficient test on each allowed reduced reciprocal factor
produces nonvanishing of the native primitive at one conjugate root.

The caller supplies the actual integral reduction map and integer clearing
rates. Neither a specific prime nor simplicity of the residue root is needed.
At ν = 1 the conclusion is the existing native first-primitive transport
slot, after rewriting X^1. -/
theorem chosen_root_cut_of_reduced_coefficients
    {E κ : Type*} [Field E] [CharZero E] [Field κ]
    (H : E[X]) (h0 : H.coeff 0 ≠ 0)
    (F : ℤ[X]) (fm : F.Monic) {a : E} (a0 : a ≠ 0)
    (corr : F.map (algebraMap ℤ E) = scaledReciprocal H a)
    (splitF : (F.map (algebraMap ℤ E)).Splits)
    (q : integralClosure ℤ E →+* κ) {ρ : κ} (ρ0 : ρ ≠ 0) (G : κ[X])
    (reduced : (F.map (algebraMap ℤ (integralClosure ℤ E))).map q =
      G * (X - C ρ))
    (d ν : ℕ) (L : ℤ) (rate : Fin (d + 1) → ℤ)
    (paid : ∀ i : Fin (d + 1), rate i * ((i.val + ν + 1 : ℕ) : ℤ) = L)
    (cut : ∀ S : κ[X], S.Monic → S.natDegree = d → S ∣ G →
      (∑ i : Fin (d + 1), (rate i : κ) * S.coeff (d - i.val) *
        ρ ^ (d - i.val)) ≠ 0) :
    ∃ v : E, H.IsRoot v ∧
      ∀ Q N : E[X], Q.natDegree = d → Q * N = H → N.IsRoot v →
        (primitive (X^ν * Q)).eval v ≠ 0 := by
  classical
  let B := integralClosure ℤ E
  let bE : B →+* E := algebraMap B E
  have inj : Function.Injective bE := fun _ _ h => Subtype.ext h
  let FB := F.map (algebraMap ℤ B)
  have fBM : FB.Monic := fm.map _
  have fMap : FB.map bE = F.map (algebraMap ℤ E) := by
    dsimp only [FB, bE]
    rw [map_map, ← IsScalarTower.algebraMap_eq ℤ B E]
  have red : FB.map q = G * (X - C ρ) := reduced
  have splitB : FB.Splits := by
    refine Splits.of_splits_map_of_injective inj (fMap.symm ▸ splitF) ?_
    intro r hr
    rw [fMap] at hr
    have ev := (mem_roots (fm.map (algebraMap ℤ E)).ne_zero).mp hr
    have eint : IsIntegral ℤ r := ⟨F, fm, by
      change aeval r F = 0
      rw [← eval_map_algebraMap F r]
      exact ev⟩
    exact ⟨⟨r, eint⟩, rfl⟩
  have rb : ρ ∈ (FB.map q).roots :=
    (mem_roots (fBM.map q).ne_zero).mpr (by rw [red]; simp [IsRoot])
  rw [splitB.roots_map_of_ne_zero (fBM.map q).ne_zero] at rb
  obtain ⟨t, ht, redt⟩ := Multiset.mem_map.mp rb
  have t0 : bE t ≠ 0 := by
    intro h
    have tb : t = 0 := inj (by simpa only [map_zero] using h)
    apply ρ0
    rw [← redt, tb, map_zero]
  have tE : (F.map (algebraMap ℤ E)).IsRoot (bE t) := by
    have root := (mem_roots fBM.ne_zero).mp ht
    rw [← fMap, IsRoot, eval_map_apply, root.eq_zero, map_zero]
  let v := a / bE t
  have vr : H.IsRoot v := (scaledReciprocal_isRoot_iff h0 a0 t0).mp (corr ▸ tE)
  refine ⟨v, vr, ?_⟩
  intro Q N qd product nroot zero
  have no : Q.coeff 0 * N.coeff 0 ≠ 0 := by
    have ce : (Q * N).coeff 0 = Q.coeff 0 * N.coeff 0 := by
      simp only [coeff_zero_eq_eval_zero, eval_mul]
    rw [← ce, product]
    exact h0
  have q0 : Q.coeff 0 ≠ 0 := fun h => no (by rw [h, zero_mul])
  have n0 : N.coeff 0 ≠ 0 := fun h => no (by rw [h, mul_zero])
  let J := scaledReciprocal Q a
  let U := scaledReciprocal N a
  have jM : J.Monic := scaledReciprocal_monic q0 a
  have uM : U.Monic := scaledReciprocal_monic n0 a
  have prodE : J * U = F.map (algebraMap ℤ E) := by
    change scaledReciprocal Q a * scaledReciprocal N a = _
    rw [← scaledReciprocal_mul, product, ← corr]
  have jLift : J ∈ Polynomial.lifts bE :=
    integralClosure.mem_lifts_of_monic_of_dvd_map E fm jM ⟨U, prodE.symm⟩
  have uLift : U ∈ Polynomial.lifts bE :=
    integralClosure.mem_lifts_of_monic_of_dvd_map E fm uM
      ⟨J, prodE.symm.trans (mul_comm J U)⟩
  obtain ⟨JB, jMap⟩ := (Polynomial.mem_lifts (f := bE) J).mp jLift
  obtain ⟨UB, uMap⟩ := (Polynomial.mem_lifts (f := bE) U).mp uLift
  have jbM : JB.Monic := inj.monic_map_iff.mpr (jMap.symm ▸ jM)
  have prodB : JB * UB = FB := by
    apply Polynomial.map_injective bE inj
    rw [Polynomial.map_mul, jMap, uMap, fMap, prodE]
  have prodR : JB.map q * UB.map q = G * (X - C ρ) := by
    rw [← Polynomial.map_mul, prodB, red]
  have uRoot : U.IsRoot (bE t) :=
    (scaledReciprocal_isRoot_iff n0 a0 t0).mpr nroot
  have ubRoot : UB.IsRoot t := by
    change UB.eval t = 0
    apply inj
    rw [← eval_map_apply, uMap, uRoot.eq_zero, map_zero]
  have urRoot : (UB.map q).IsRoot ρ := by
    rw [← redt, IsRoot, eval_map_apply, ubRoot.eq_zero, map_zero]
  have du : (X - C ρ) ∣ UB.map q := dvd_iff_isRoot.mpr urRoot
  obtain ⟨U₁, uFactor⟩ := du
  have dj : JB.map q ∣ G := by
    refine ⟨U₁, ?_⟩
    apply mul_right_cancel₀ (X_sub_C_ne_zero ρ)
    calc
      _ = JB.map q * UB.map q := prodR.symm
      _ = _ := by rw [uFactor]; ring
  have jd : JB.natDegree = d := by
    rw [← natDegree_map_eq_of_injective inj JB, jMap]
    exact (scaledReciprocal_degree q0 a).trans qd
  have zb : coefficientSum rate JB t = 0 := by
    apply inj
    rw [map_coefficientSum, map_zero, jMap]
    exact coefficientSum_of_primitive_zero ν L rate paid qd q0 a0 t0 zero
  have zr : coefficientSum rate (JB.map q) (q t) = 0 := by
    rw [← map_coefficientSum, zb, map_zero]
  apply cut (JB.map q) (jbM.map q) ((jbM.natDegree_map q).trans jd) dj
  simpa only [coefficientSum, redt] using zr

end
end RKResearch.Certified.Graded.NativeReciprocal
