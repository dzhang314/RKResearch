module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fintype.EquivFin
public import RKCert.ReviewedNative.GradedSeparation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # A rational degree-six quadrature cannot use only four physical clocks

The monic four-clock annihilator would be in the degree-three/four shifted
Legendre pencil. Its primitive projective reduction modulo 19 has an
irreducible factor of degree greater than one in every direction. The
argument keeps denominator-zero clock reductions as projective infinity.
-/

namespace RKResearch.Certified.RationalFourClock
open Polynomial
open scoped BigOperators

noncomputable def L3 (R : Type*) [CommRing R] : R[X] :=
  C 20 * X^3 - C 30 * X^2 + C 12 * X - C 1

noncomputable def L4 (R : Type*) [CommRing R] : R[X] :=
  C 70 * X^4 - C 140 * X^3 + C 90 * X^2 - C 20 * X + C 1

def p3 {R : Type*} [CommRing R] (x : R) :=
  20*x^3 - 30*x^2 + 12*x - 1
def p4 {R : Type*} [CommRing R] (x : R) :=
  70*x^4 - 140*x^3 + 90*x^2 - 20*x + 1
private def d3 {R : Type*} [CommRing R] (x : R) := 60*x^2 - 60*x + 12
private def d4 {R : Type*} [CommRing R] (x : R) := 280*x^3 - 420*x^2 + 180*x - 20

@[simp] theorem eval_L3 {R : Type*} [CommRing R] (x : R) :
    (L3 R).eval x = p3 x := by simp [L3,p3]
@[simp] theorem eval_L4 {R : Type*} [CommRing R] (x : R) :
    (L4 R).eval x = p4 x := by simp [L4,p4]

private theorem derivative_L3 {R : Type*} [CommRing R] (x : R) :
    (L3 R).derivative.eval x = d3 x := by
  simp [L3,d3,Polynomial.derivative_mul,Polynomial.derivative_pow]; ring
private theorem derivative_L4 {R : Type*} [CommRing R] (x : R) :
    (L4 R).derivative.eval x = d4 x := by
  simp [L4,d4,Polynomial.derivative_mul,Polynomial.derivative_pow]; ring

local instance : Fact (Nat.Prime 19) := ⟨by decide⟩
private abbrev F := ZMod 19

private noncomputable def fiber (f : F→F) : Finset F :=
  Finset.univ.filter (fun x => f x=0)

private theorem mod19_finite :
    (∀ t : F, ((Finset.univ.filter (fun x : F => p4 x+t*p3 x=0)).card ≤ 2) ∧
      (∀ x : F, p4 x+t*p3 x=0 → d4 x+t*d3 x≠0)) ∧
    ((Finset.univ.filter (fun x : F => p3 x=0)).card ≤ 1) ∧
      (∀ x : F, p3 x=0 → d3 x≠0) := by
  decide +kernel

private theorem nodup_roots_of_no_derivative_root {P : F[X]} (hP : P≠0)
    (h : ∀ x : F, P.eval x=0 → P.derivative.eval x≠0) :
    P.roots.Nodup := by
  rw [Multiset.nodup_iff_count_le_one]
  intro x
  rw [Polynomial.count_roots]
  by_contra hh
  have hz := (one_lt_rootMultiplicity_iff_isRoot hP).mp (lt_of_not_ge hh)
  exact h x hz.1 hz.2

private theorem roots_card_le_fiber {P : F[X]} (hP : P≠0)
    (h : ∀ x : F, P.eval x=0 → P.derivative.eval x≠0) :
    P.roots.card ≤ (fiber P.eval).card := by
  have no := nodup_roots_of_no_derivative_root hP h
  have sub : P.roots.toFinset ⊆ fiber P.eval := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Polynomial.mem_roots hP).mp
      (Multiset.mem_toFinset.mp hx)⟩
  have le := Finset.card_le_card sub
  rw [Multiset.toFinset_card_of_nodup no] at le
  exact le

private theorem degree_L3 : (L3 F).natDegree=3 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · unfold L3; compute_degree
  · norm_num [L3,coeff_sub,coeff_add,coeff_C_mul,coeff_X_pow,coeff_one]
    decide +kernel

private theorem degree_finite (t : F) : (L4 F + C t * L3 F).natDegree=4 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · unfold L3 L4; compute_degree
  · norm_num [L3,L4,coeff_sub,coeff_add,coeff_C_mul,coeff_X_pow,coeff_one]
    decide +kernel

private theorem mod19_L3_not_split : ¬ (L3 F).Splits := by
  intro hs
  have hP : L3 F ≠ 0 := by
    have hd := degree_L3
    intro e
    rw [e,natDegree_zero] at hd
    omega
  have h := roots_card_le_fiber hP (fun x e => by
    rw [derivative_L3]
    exact mod19_finite.2.2 x (by simpa using e))
  rw [←hs.natDegree_eq_card_roots,degree_L3] at h
  have hc : (fiber (L3 F).eval).card ≤ 1 := by
    simpa only [fiber,eval_L3] using mod19_finite.2.1
  omega

private theorem mod19_finite_not_split (t : F) : ¬ (L4 F+C t*L3 F).Splits := by
  intro hs
  have hd := degree_finite t
  have hP : L4 F+C t*L3 F ≠ 0 := by intro e; rw [e,natDegree_zero] at hd; omega
  have h := roots_card_le_fiber hP (fun x e => by
    simp only [eval_add,eval_mul,eval_C,eval_L3,eval_L4] at e
    simp only [derivative_add,derivative_mul,derivative_C,zero_mul,zero_add,
      eval_add,eval_mul,eval_C,derivative_L3,derivative_L4]
    exact (mod19_finite.1 t).2 x e)
  rw [←hs.natDegree_eq_card_roots,hd] at h
  have hc : (fiber (L4 F+C t*L3 F).eval).card ≤ 2 := by
    simpa only [fiber,eval_add,eval_mul,eval_C,eval_L3,eval_L4] using (mod19_finite.1 t).1
  omega

private theorem not_both_mod19_zero (x : ℚ)
    (ha : (x.num : F)=0) (hb : (x.den : F)=0) : False := by
  have han : 19 ∣ x.num.natAbs := by
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd x.num 19).mp ha
    simpa using (Int.natAbs_dvd_natAbs.mpr hd)
  have hbn := (ZMod.natCast_eq_zero_iff x.den 19).mp hb
  have hboth := Nat.dvd_gcd han hbn
  rw [x.reduced.gcd_eq_one] at hboth
  exact (by decide : ¬ 19 ∣ 1) hboth

private theorem C_mul_splits_iff {a : F} (ha : a≠0) {P : F[X]} :
    (C a * P).Splits ↔ P.Splits := by
  constructor
  · intro h
    have hh := (Splits.C (a⁻¹ : F)).mul h
    rwa [←mul_assoc,←C_mul,inv_mul_cancel₀ ha,map_one,one_mul] at hh
  · exact fun h => (Splits.C a).mul h

private theorem mod19_pencil_not_split (a b : F) (h : a≠0 ∨ b≠0) :
    ¬ (C a*L4 F+C b*L3 F).Splits := by
  by_cases ha : a=0
  · have hb := h.resolve_left (not_not_intro ha)
    simpa only [ha,map_zero,zero_mul,zero_add,C_mul_splits_iff hb] using mod19_L3_not_split
  · have e : C a * (L4 F+C (b/a)*L3 F) = C a*L4 F+C b*L3 F := by
      rw [mul_add,←mul_assoc,←C_mul,mul_div_cancel₀ _ ha]
    rw [←e,C_mul_splits_iff ha]
    exact mod19_finite_not_split _

private noncomputable def rationalLin {R : Type*} [CommRing R] (a b : R) : R[X] :=
  C a*X-C b

private theorem rationalLin_mod19_nonzero (q : ℚ) :
    rationalLin (q.den : F) (q.num : F) ≠ 0 := by
  intro e
  have e0 := congrArg (fun p : F[X] => p.coeff 0) e
  have e1 := congrArg (fun p : F[X] => p.coeff 1) e
  simp only [rationalLin,coeff_sub,coeff_C_mul,coeff_X_zero,coeff_C_zero,
    mul_zero,zero_sub,coeff_zero,neg_eq_zero] at e0
  simp only [rationalLin,coeff_sub,coeff_C_mul,coeff_X_one,
    coeff_C_of_ne_zero one_ne_zero,mul_one,sub_zero,coeff_zero] at e1
  exact not_both_mod19_zero q e0 e1

private theorem rationalLin_mod19_split (q : ℚ) :
    (rationalLin (q.den : F) (q.num : F)).Splits := by
  by_cases h : (q.den:F)=0
  · rw [rationalLin,h,map_zero,zero_mul,zero_sub,←C_neg]
    exact Splits.C _
  · have e : rationalLin (q.den : F) (q.num : F) =
      C (q.den : F) * (X-C ((q.num:F)/(q.den:F))) := by
      rw [rationalLin,mul_sub,←C_mul,mul_div_cancel₀ _ h]
    rw [e]
    exact (Splits.C _).mul (Splits.X_sub_C _)

private theorem map_pencil {R S : Type*} [CommRing R] [CommRing S] (f : R→+* S)
    (a b : R) : (C a*L4 R+C b*L3 R).map f = C (f a)*L4 S+C (f b)*L3 S := by
  simp [L3,L4,Polynomial.map_pow,map_ofNat]
private theorem map_rationalLin {R S : Type*} [CommRing R] [CommRing S] (f : R→+* S)
    (a b : R) : (rationalLin a b).map f = rationalLin (f a) (f b) := by simp [rationalLin]

private theorem pencil_mod19_nonzero {a b : F} (hne : a≠0 ∨ b≠0) :
    C a*L4 F+C b*L3 F ≠ 0 := by
  intro h
  exact mod19_pencil_not_split a b hne (h.symm ▸ Splits.zero)

theorem rational_four_factor_pencil_impossible (c : Fin 4→ℚ) (lam : ℚ)
    (h : C (70:ℚ) * (∏ i, (X-C (c i))) = L4 ℚ+C lam*L3 ℚ) : False := by
  let a : ℤ := lam.den
  let b : ℤ := lam.num
  let U : ℤ[X] := C a*L4 ℤ+C b*L3 ℤ
  let V : ℤ[X] := ∏ i, rationalLin ((c i).den : ℤ) (c i).num
  let u : ℚ := 70 * (a : ℚ) / ∏ i, ((c i).den : ℚ)
  have per (q : ℚ) : (rationalLin (q.den : ℤ) q.num).map (Int.castRingHom ℚ) =
      C (q.den : ℚ) * (X-C q) := by
    rw [map_rationalLin]
    simp only [Int.coe_castRingHom,Int.cast_natCast]
    rw [rationalLin,mul_sub,←C_mul]
    have e : (q.den : ℚ)*q=(q.num:ℚ) := by
      calc
        (q.den:ℚ)*q = (q.den:ℚ)*((q.num:ℚ)/(q.den:ℚ)) :=
          congrArg (fun z : ℚ => (q.den:ℚ)*z) q.num_div_den.symm
        _ = _ := mul_div_cancel₀ _ (show (q.den:ℚ)≠0 by exact_mod_cast q.den_nz)
    rw [e]
  have hden : (∏ i, ((c i).den : ℚ))≠0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => by exact_mod_cast (c i).den_nz)
  have hU : U.map (Int.castRingHom ℚ) = C (a : ℚ) * (L4 ℚ+C lam*L3 ℚ) := by
    dsimp only [U]
    rw [map_pencil]
    simp only [Int.coe_castRingHom]
    rw [mul_add,←mul_assoc,←C_mul]
    have e : (a:ℚ)*lam=(b:ℚ) := by
      dsimp [a,b]
      push_cast
      calc
        (lam.den:ℚ)*lam = (lam.den:ℚ)*((lam.num:ℚ)/(lam.den:ℚ)) :=
          congrArg (fun z : ℚ => (lam.den:ℚ)*z) lam.num_div_den.symm
        _ = _ := mul_div_cancel₀ _ (show (lam.den:ℚ)≠0 by exact_mod_cast lam.den_nz)
    rw [e]
  have hV : V.map (Int.castRingHom ℚ) =
      C (∏ i, ((c i).den : ℚ)) * (∏ i, (X-C (c i))) := by
    dsimp only [V]
    rw [Polynomial.map_prod]
    simp_rw [per]
    rw [Finset.prod_mul_distrib,map_prod]
  have he : C u * V.map (Int.castRingHom ℚ) = U.map (Int.castRingHom ℚ) := by
    rw [hU,hV,←mul_assoc,←C_mul]
    dsimp [u]
    rw [div_mul_cancel₀ _ hden,C_mul,mul_comm (C (70:ℚ)),mul_assoc,h]
  have hI : C u.num * V = C (u.den : ℤ) * U := by
    apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
    simp only [Polynomial.map_mul,map_C,Int.coe_castRingHom, Int.cast_natCast]
    have e : (u.den : ℚ)*u=(u.num:ℚ) := by
      calc
        (u.den:ℚ)*u = (u.den:ℚ)*((u.num:ℚ)/(u.den:ℚ)) :=
          congrArg (fun z : ℚ => (u.den:ℚ)*z) u.num_div_den.symm
        _ = _ := mul_div_cancel₀ _ (show (u.den:ℚ)≠0 by exact_mod_cast u.den_nz)
    rw [←e,C_mul,mul_assoc,he]
  have hF := congrArg (Polynomial.map (Int.castRingHom F)) hI
  simp only [Polynomial.map_mul,map_C,Int.coe_castRingHom,Int.cast_natCast] at hF
  have hPV : V.map (Int.castRingHom F) = ∏ i, rationalLin ((c i).den : F) ((c i).num : F) := by
    simp [V,Polynomial.map_prod,map_rationalLin]
  have hv0 : V.map (Int.castRingHom F) ≠ 0 := by
    rw [hPV]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => rationalLin_mod19_nonzero (c i))
  have hsv : (V.map (Int.castRingHom F)).Splits := by
    rw [hPV]
    exact Splits.prod (fun i _ => rationalLin_mod19_split (c i))
  have hU_eq : U.map (Int.castRingHom F) = C (lam.den : F)*L4 F+C (lam.num:F)*L3 F := by
    dsimp only [U]
    rw [map_pencil]
    simp [a,b]
  have hne : (lam.den:F)≠0 ∨ (lam.num:F)≠0 := by
    by_contra h; push Not at h
    exact not_both_mod19_zero lam h.2 h.1
  have hU0 : U.map (Int.castRingHom F) ≠ 0 := by
    rw [hU_eq]; exact pencil_mod19_nonzero hne
  have hu : (u.num : F)≠0 := by
    intro z
    rw [z,map_zero,zero_mul] at hF
    have e := (mul_eq_zero.mp hF.symm).resolve_right hU0
    exact not_both_mod19_zero u z (C_eq_zero.mp e)
  have hd : (u.den : F)≠0 := by
    intro z
    rw [z,map_zero,zero_mul] at hF
    have e := (mul_eq_zero.mp hF).resolve_right hv0
    exact hu (C_eq_zero.mp e)
  have hs : (C (u.den : F) * U.map (Int.castRingHom F)).Splits :=
    hF ▸ (Splits.C (u.num:F)).mul hsv
  have hsU := (C_mul_splits_iff hd).mp hs
  rw [hU_eq] at hsU
  exact mod19_pencil_not_split _ _ hne hsU

end RKResearch.Certified.RationalFourClock
