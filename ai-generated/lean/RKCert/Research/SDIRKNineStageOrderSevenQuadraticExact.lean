module

public import RKCert.Research.SDIRKNineStageOrderSevenQuadratic

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Exactness of the quadratic nine-stage tableau in all specializations

The tall and bush order-eight failures have norms whose integer
Bézout combination is 11. This already maps to a unit when the
stage normalization denominator maps to a unit. -/

namespace RKResearch.Certified.SDIRKNineStageOrderSevenQuadraticExact

open FiniteRootedTree SDIRKNineStageOrderSevenQuadratic
open scoped Matrix

def tallDefect : K := ⟨-566828049,156338⟩
private def tallConjugate : K := ⟨-566828049,-156338⟩
def tallNorm : ℕ := 310711594906171965

private theorem tall_norm_identity :
    tallDefect*tallConjugate = (tallNorm : K) := by decide +kernel

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 24000 in
theorem eighth_tall_relation :
    (957274560 : K) *
        (((tallTree 8).factorial : K) * (bNum ⬝ᵥ Φ (tallTree 8) ANum) -
          (bDen : K) * (aDen : K)^7) =
    ((bDen : K) * (aDen : K)^7) * tallDefect := by
  decide +kernel

private theorem numeratorTriangular : ANum.IsLowerTriangular := by
  change ∀ i j : Fin 9, i < j → ANum i j = 0
  simp only [ANum, Matrix.of_apply]
  decide +kernel

private theorem numeratorDiagonal (i : Fin 9) : ANum i i = (gNum : K) := by
  simp [ANum]

private theorem exists_exact_tall_norm {R : Type*} [CommRing R] {ρ : R}
    (hr : ρ * ρ = (radicand : R))
    (hd : IsUnit (aDen : R)) (he : IsUnit (bDen : R))
    (hn : (tallNorm : R) ≠ 0) :
    ∃ (A : Matrix (Fin 9) (Fin 9) R) (b : Fin 9 → R) (γ : R),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ IsUnit γ ∧ (4 : R) * γ = 1 ∧
      HasOrder 7 A b ∧ ¬ HasOrder 8 A b := by
  have hρ : ρ * ρ = radicand • (1 : R) + (0 : ℤ) • ρ := by simpa [Algebra.smul_def] using hr
  let f : K →+* R := (QuadraticAlgebra.lift ⟨ρ,hρ⟩).toRingHom
  obtain ⟨du, hdu⟩ := hd
  obtain ⟨eu, heu⟩ := he
  let A : Matrix (Fin 9) (Fin 9) R := ((↑du⁻¹ : R)) • ANum.map f
  let b : Fin 9 → R := ((↑eu⁻¹ : R)) • (f ∘ bNum)
  let γ : R := (↑du⁻¹ : R) * (gNum : R)
  have hA : ANum.map f = f (aDen : K) • A := by
    ext i j
    simp only [map_natCast]
    change f (ANum i j) = (aDen : R) * ((↑du⁻¹ : R) * f (ANum i j))
    rw [← hdu, ← mul_assoc]
    simp
  have hb : f ∘ bNum = f (bDen : K) • b := by
    funext i
    simp only [map_natCast]
    change f (bNum i) = (bDen : R) * ((↑eu⁻¹ : R) * f (bNum i))
    rw [← heu, ← mul_assoc]
    simp
  have hds : IsUnit (f (aDen : K)) := by rw [map_natCast, ← hdu]; exact du.isUnit
  have hes : IsUnit (f (bDen : K)) := by rw [map_natCast, ← heu]; exact eu.isUnit
  have h4n : (4 : ℕ) * gNum = aDen := by decide +kernel
  have h4 : (4 : R) * γ = 1 := by
    have h4r : (4 : R) * (gNum : R) = (aDen : R) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using congrArg (Nat.cast : ℕ → R) h4n
    change (4 : R) * ((↑du⁻¹ : R) * (gNum : R)) = 1
    rw [mul_left_comm, h4r, ← hdu]
    simp
  refine ⟨A,b,γ,?_,?_,IsUnit.of_mul_eq_one 4 (by rw [mul_comm, h4]),h4,?_,?_⟩
  · intro i j hij
    change (↑du⁻¹ : R) * f (ANum i j) = 0
    rw [numeratorTriangular hij, map_zero, mul_zero]
  · intro i
    change (↑du⁻¹ : R) * f (ANum i i) = γ
    rw [numeratorDiagonal, map_natCast]
  · exact hasOrder_of_scaled_check f (fun _ => rfl) (fun _ => rfl) hA hb hds hes checked
  · intro H
    have ho := H (tallTree 8) (by rw [order_tallTree]; decide)
    have hh := congrArg f eighth_tall_relation
    simp only [map_mul, map_sub, map_pow, map_natCast, RingHom.map_dotProduct, RKResearch.map_Φ,
      hA, hb, Φ_matrix_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, order_tallTree] at hh
    rw [show (((8 : ℕ+) : ℕ) - 1) = 7 by decide +kernel] at hh
    have hΩ : IsUnit ((bDen : R) * (aDen : R)^7) := by
      simpa only [map_natCast] using hes.mul (hds.pow 7)
    have zero : ((bDen : R) * (aDen : R)^7) * f tallDefect = 0 := by
      rw [← hh]
      have hEl :
          ((tallTree 8).factorial : R) * ((aDen : R)^7 * ((bDen : R) *
            (b ⬝ᵥ Φ (tallTree 8) A))) = (bDen : R) * (aDen : R)^7 := by
        linear_combination (norm := ring) ((bDen : R) * (aDen : R)^7) * ho
      rw [hEl,sub_self,mul_zero]
    have hf0 : f tallDefect = 0 := hΩ.mul_left_cancel (zero.trans (mul_zero _).symm)
    apply hn
    have hc := congrArg f tall_norm_identity
    rw [map_mul, map_natCast, hf0, zero_mul] at hc
    exact hc.symm



theorem stage_denominator_has_eleven : (11 : ℕ) * (aDen/11)=aDen := by
  decide +kernel

theorem norm_bezout_Z :
    (2861460114013366:ℤ)*(defectNorm:ℤ) -
      (14237538492914339107:ℤ)*(tallNorm:ℤ)=11 := by
  decide +kernel

/-- No norm guard remains. The source tableau is exactly order seven
over every nonzero target where the two published scales are units. -/
theorem exists_exact_of_root {R : Type*} [CommRing R] [Nontrivial R] {ρ : R}
    (hr : ρ*ρ=(radicand : R)) (hd : IsUnit (aDen:R)) (he : IsUnit (bDen:R)) :
    ∃ (A : Matrix (Fin 9) (Fin 9) R) (b : Fin 9 → R) (γ : R),
      A.IsLowerTriangular ∧ (∀ i,A i i=γ) ∧ IsUnit γ ∧ (4:R)*γ=1 ∧
      HasOrder 7 A b ∧ ¬HasOrder 8 A b := by
  by_cases hn : (defectNorm:R)=0
  · have eq : (11:R)*((aDen/11:ℕ):R)=(aDen:R) := by
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using
        congrArg (Nat.cast : ℕ→R) stage_denominator_has_eleven
    have hU : IsUnit (11:R) := by
      rw [←eq] at hd
      exact isUnit_of_mul_isUnit_left hd
    have ht : (tallNorm:R)≠0 := by
      intro h
      have e := congrArg (Int.castRingHom R) norm_bezout_Z
      simp only [map_mul,map_sub,Int.coe_castRingHom,Int.cast_natCast,Int.cast_ofNat,hn,h,
        mul_zero,sub_self] at e
      exact hU.ne_zero e.symm
    exact exists_exact_tall_norm hr hd he ht
  · exact SDIRKNineStageOrderSevenQuadratic.exists_exact_of_root hr hd he hn

/-- Integer digit lifting of a simple quadratic root. The parameter j is
a chosen inverse of the derivative modulo p. No p-adic completeness
is necessary for the nilpotent-ring specialization. -/
theorem lift_root (p : ℕ) (a j v₀ v₁ : ℤ)
    (base : a^2-radicand=(p:ℤ)*v₀)
    (step : 1-2*a*j=(p:ℤ)*v₁) (k : ℕ) :
    ∃ t v : ℤ, (a+(p:ℤ)*t)^2-radicand=(p:ℤ)^(k+1)*v := by
  induction k with
  | zero =>
      refine ⟨0,v₀,?_⟩
      simpa using base
  | succ k ih =>
      obtain ⟨t,v,h⟩ := ih
      refine ⟨t-j*(p:ℤ)^k*v, (v₁-2*j*t)*v+j^2*(p:ℤ)^k*v^2, ?_⟩
      rw [show k.succ+1=k+1+1 by omega,
        pow_succ (p:ℤ) (k+1),pow_succ (p:ℤ) k]
      rw [pow_succ (p:ℤ) k] at h
      linear_combination (norm := ring) h + ((p:ℤ)^k*(p:ℤ)*v)*step

private theorem unit_in_nilpotent_power {R : Type*} [CommRing R] (p k n : ℕ)
    (h0 : (p:R)^(k+1)=0) (hc : n.Coprime p) : IsUnit (n:R) := by
  have hm : ((p^(k+1):ℕ):R)=0 := by simpa using h0
  let f : ZMod (p^(k+1)) →+* R := ZMod.castHom (ringChar.dvd hm) R
  have hu : IsUnit (n:ZMod (p^(k+1))) :=
    (ZMod.isUnit_iff_coprime _ _).mpr (hc.pow_right (k+1))
  simpa only [map_natCast] using hu.map f

theorem exists_exact_of_nilpotent_simple_root (R : Type*) [CommRing R] [Nontrivial R]
    (p : ℕ) (a j v₀ v₁ : ℤ)
    (base : a^2-radicand=(p:ℤ)*v₀) (step : 1-2*a*j=(p:ℤ)*v₁)
    (hd : aDen.Coprime p) (he : bDen.Coprime p) (hp : IsNilpotent (p:R)) :
    ∃ (A : Matrix (Fin 9) (Fin 9) R) (b : Fin 9 → R) (γ : R),
      A.IsLowerTriangular ∧ (∀ i,A i i=γ) ∧ IsUnit γ ∧ (4:R)*γ=1 ∧
      HasOrder 7 A b ∧ ¬HasOrder 8 A b := by
  obtain ⟨k,hk⟩ := hp
  have hz : (p:R)^(k+1)=0 := by rw [pow_succ,hk,zero_mul]
  obtain ⟨t,v,h⟩ := lift_root p a j v₀ v₁ base step k
  have hr : (((a+(p:ℤ)*t : ℤ):R))*(((a+(p:ℤ)*t : ℤ):R))=(radicand:R) := by
    have cast := congrArg (Int.castRingHom R) h
    simp only [map_sub,map_mul,map_pow,Int.coe_castRingHom,Int.cast_natCast,hz,zero_mul] at cast
    simpa only [pow_two] using sub_eq_zero.mp cast
  exact exists_exact_of_root hr (unit_in_nilpotent_power p k _ hz hd)
    (unit_in_nilpotent_power p k _ hz he)

/-- An additional exact nine-stage upper, including every positive power of 4217. -/
theorem exists_exact_of_4217_nilpotent (R : Type*) [CommRing R] [Nontrivial R]
    (h : IsNilpotent (4217:R)) :
    ∃ (A : Matrix (Fin 9) (Fin 9) R) (b : Fin 9 → R) (γ : R),
      A.IsLowerTriangular ∧ (∀ i,A i i=γ) ∧ IsUnit γ ∧ (4:R)*γ=1 ∧
      HasOrder 7 A b ∧ ¬HasOrder 8 A b :=
  exists_exact_of_nilpotent_simple_root R 4217 1262 680 275 (-407)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

/-- An additional exact nine-stage upper, including every positive power of 27367649. -/
theorem exists_exact_of_27367649_nilpotent (R : Type*) [CommRing R] [Nontrivial R]
    (h : IsNilpotent (27367649:R)) :
    ∃ (A : Matrix (Fin 9) (Fin 9) R) (b : Fin 9 → R) (γ : R),
      A.IsLowerTriangular ∧ (∀ i,A i i=γ) ∧ IsUnit γ ∧ (4:R)*γ=1 ∧
      HasOrder 7 A b ∧ ¬HasOrder 8 A b :=
  exists_exact_of_nilpotent_simple_root R 27367649 9030753 7225113 2979960 (-4768273)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h


def mixedPrimaryModulus : ℕ := 115409375833

theorem mixedPrimaryModulus_eq : mixedPrimaryModulus = (4217:ℕ)*27367649 := by
  decide +kernel

private def unitPart : ℕ := 13395643547

private theorem norm_split : defectNorm=unitPart*mixedPrimaryModulus := by
  decide +kernel

private theorem unit_part_divides :
    unitPart * (((aDen*bDen)^2)/unitPart)=(aDen*bDen)^2 := by
  decide +kernel

/-- On the allowed scale locus the old bushy norm guard fails exactly
when the product of the two exceptional primes vanishes. -/
theorem original_norm_zero_iff {R : Type*} [CommRing R] (hd : IsUnit (aDen:R))
    (he : IsUnit (bDen:R)) : (defectNorm:R)=0 ↔ (mixedPrimaryModulus:R)=0 := by
  have hProd :
      (unitPart:R)*((((aDen*bDen)^2)/unitPart:ℕ):R) = ((aDen:R)*(bDen:R))^2 := by
    simpa only [Nat.cast_mul,Nat.cast_pow] using congrArg (Nat.cast : ℕ→R) unit_part_divides
  have hu : IsUnit (unitPart:R) := by
    have h := (hd.mul he).pow 2
    rw [←hProd] at h
    exact isUnit_of_mul_isUnit_left h
  have e : (defectNorm:R)=(unitPart:R)*(mixedPrimaryModulus:R) := by
    simpa only [Nat.cast_mul] using congrArg (Nat.cast : ℕ→R) norm_split
  rw [e]
  constructor
  · intro h
    exact hu.mul_left_cancel (h.trans (mul_zero _).symm)
  · intro h
    rw [h,mul_zero]

/-- The same witness also works on arbitrary mixtures of the two
new primary characteristics, not just on a single prime-power tower. -/
theorem exists_exact_of_mixed_primary_nilpotent (R : Type*) [CommRing R] [Nontrivial R]
    (h : IsNilpotent (mixedPrimaryModulus:R)) :
    ∃ (A : Matrix (Fin 9) (Fin 9) R) (b : Fin 9 → R) (γ : R),
      A.IsLowerTriangular ∧ (∀ i,A i i=γ) ∧ IsUnit γ ∧ (4:R)*γ=1 ∧
      HasOrder 7 A b ∧ ¬HasOrder 8 A b :=
  exists_exact_of_nilpotent_simple_root R mixedPrimaryModulus 100201993742 94261408269
    86998473715 (-163681346915)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

end RKResearch.Certified.SDIRKNineStageOrderSevenQuadraticExact
