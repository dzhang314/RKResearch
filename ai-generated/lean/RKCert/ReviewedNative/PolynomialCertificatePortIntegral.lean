module

public import RKCert.ReviewedNative.PolynomialCertificatePortDiagonal
public import RKCert.NodalPrimitive
public import Mathlib.Data.Int.Cast.Field
public import Mathlib.Data.List.Forall2

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Integer vertex sign certificates for actual formal unit integrals -/

namespace RKCert.ReviewedNative.PolynomialCertificate

open Polynomial RKCert.Endpoint
open scoped Polynomial

/-- All endpoint vectors in the order of the factor list. Repeated or
degenerate endpoints are harmless because the predicate is universal. -/
def factorCorners : List (ℤ × ℤ) → List (List ℤ)
  | [] => [[]]
  | a :: bs => (factorCorners bs).map (a.1 :: ·) ++ (factorCorners bs).map (a.2 :: ·)

def intMoment (den e : ℕ) : ℤ := ((den / (e + 1) : ℕ) : ℤ)

def vertexPortOK (positive : Bool) (e : ℕ) (l u : ℤ) (rs : List ℤ) : Bool :=
  let M := (e + rs.length + 1).factorial
  (List.range (rs.length + 1)).all fun j =>
    let z := diagonalCoeff (intMoment M) l u rs e j
    if positive then decide (0 < z) else decide (z < 0)

def boxPortOK (positive : Bool) (e : ℕ) (l u : ℤ) (boxes : List (ℤ × ℤ)) : Bool :=
  (factorCorners boxes).all (vertexPortOK positive e l u)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def unitMoment (e : ℕ) : K := 1 / ((e + 1 : ℕ) : K)

noncomputable def unitFunctional : K[X] →ₗ[K] K := (Polynomial.leval 1).comp formalPrimitiveLinear

noncomputable def portFactor (d r : K) : K[X] := C d * X - C r

/-- The link to the actual RK port, rather than a coefficient model. -/
noncomputable def formalPort (e : ℕ) (d : K) (rs : List K) : K :=
  unitFunctional (X ^ e * (rs.map (portFactor d)).prod)

theorem formalPort_eq_rec (e : ℕ) (d : K) (rs : List K) :
    formalPort e d rs = portRec (unitMoment (K := K)) d rs e := by
  induction rs generalizing e with
  | nil =>
    change (formalPrimitive ((X : K[X]) ^ e * ([] : List K[X]).prod)).eval 1 = unitMoment e
    simp only [List.prod_nil, mul_one, X_pow_eq_monomial]
    simp [formalPrimitive, support_monomial e (one_ne_zero : (1 : K) ≠ 0), unitMoment]
  | cons r rs ih =>
    let p := (rs.map (portFactor d)).prod
    have alg : (X : K[X]) ^ e * (portFactor d r * p) =
        d • (X ^ (e + 1) * p) - r • (X ^ e * p) := by
      simp only [portFactor, Polynomial.smul_eq_C_mul, pow_succ]
      ring
    change unitFunctional (X ^ e * (portFactor d r * p)) = _
    rw [alg, map_sub, map_smul, map_smul]
    change d * formalPort (e + 1) d rs - r * formalPort e d rs = _
    rw [ih (e + 1), ih e, portRec]

theorem diagonalCoeff_intCast (mu : ℕ → ℤ) (l u : ℤ) (rs : List ℤ) (e j : ℕ) :
    diagonalCoeff (fun k => (mu k : K)) (l : K) (u : K) (rs.map (fun r : ℤ => (r : K))) e j =
      ((diagonalCoeff (R := ℤ) mu l u rs e j : ℤ) : K) := by
  induction rs generalizing e j with
  | nil => by_cases hj : j = 0 <;> simp [diagonalCoeff, hj]
  | cons r rs ih => cases j <;> simp [diagonalCoeff, shiftCoeff, ih]

private theorem intMoment_cast {M k : ℕ} (hd : k + 1 ∣ M) :
    (intMoment M k : K) = (M : K) * unitMoment k := by
  rw [unitMoment, mul_one_div, eq_div_iff (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k))]
  simpa only [intMoment, Int.cast_natCast, ← Nat.cast_mul, Nat.div_mul_cancel hd]

private theorem vertex_integer_sign {positive : Bool} {e : ℕ} {l u : ℤ} {rs : List ℤ}
    (ok : vertexPortOK positive e l u rs = true) (j : ℕ) (hj : j ≤ rs.length) :
    0 < signedValue positive
      (diagonalCoeff (fun k => (intMoment (e + rs.length + 1).factorial k : K))
        (l : K) (u : K) (rs.map (fun r : ℤ => (r : K))) e j) := by
  rw [diagonalCoeff_intCast]
  have ht := List.all_eq_true.mp ok j (List.mem_range.mpr (Nat.lt_succ_of_le hj))
  cases positive with
  | true =>
    have a : 0 < diagonalCoeff (intMoment (e + rs.length + 1).factorial) l u rs e j :=
      of_decide_eq_true ht
    have ab : (0 : K) <
        ((diagonalCoeff (R := ℤ) (intMoment (e + rs.length + 1).factorial) l u rs e j : ℤ) : K) :=
      Int.cast_pos.mpr a
    simpa only [signedValue, if_true] using ab
  | false =>
    have a : diagonalCoeff (intMoment (e + rs.length + 1).factorial) l u rs e j < 0 :=
      of_decide_eq_true ht
    have ab :
        ((diagonalCoeff (R := ℤ) (intMoment (e + rs.length + 1).factorial) l u rs e j : ℤ) : K) < 0 :=
      Int.cast_lt_zero.mpr a
    simpa only [signedValue, Bool.false_eq_true, if_false] using (neg_pos.mpr ab)

/-- A witness on one true factor vertex extends to the entire independent
stop interval. Factor coordinates are still in grid units, not divided by B. -/
theorem vertexPortOK_sound {positive : Bool} {e : ℕ} {l u : ℤ} {rs : List ℤ}
    (ok : vertexPortOK positive e l u rs = true) {d : K} (hd : d ∈ Set.Icc (l : K) (u : K)) :
    0 < signedValue positive (formalPort e d (rs.map (fun r : ℤ => (r : K)))) := by
  let M := (e + rs.length + 1).factorial
  let a := rs.map (fun r : ℤ => (r : K))
  have hM : (0 : K) < (M : K) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hsum : 0 < signedValue positive (portRec (fun k => (intMoment M k : K)) d a e) := by
    apply signed_portRec_pos_of_coeff _ _ _ _ _ _ hd
    intro j hj
    exact vertex_integer_sign ok j (by simpa [a] using hj)
  have eqn : portRec (fun k => (intMoment M k : K)) d a e =
      (M : K) * portRec (unitMoment (K := K)) d a e := by
    rw [← portRec_scale_moments]
    apply portRec_congr_moments
    intro k _ hk
    have hlen : a.length = rs.length := by simp [a]
    apply intMoment_cast
    apply Nat.dvd_factorial (Nat.zero_lt_succ k)
    rw [hlen] at hk
    omega
  rw [eqn] at hsum
  rw [formalPort_eq_rec]
  change 0 < signedValue positive (portRec _ d a e)
  cases positive with
  | true => exact pos_of_mul_pos_right hsum hM.le
  | false =>
    change 0 < -((M : K) * portRec _ d a e) at hsum
    rw [← mul_neg] at hsum
    exact pos_of_mul_pos_right hsum hM.le

private theorem signedMix (positive : Bool) : MixClosed (fun z : K => 0 < signedValue positive z) := by
  cases positive with
  | true => exact mixClosed_strictLower (0 : K)
  | false =>
    intro x y t t0 t1 hx hy
    exact neg_pos.mpr (mixClosed_strictUpper (0 : K) t0 t1 (neg_pos.mp hx) (neg_pos.mp hy))

private theorem product_corners {boxes : List (ℤ × ℤ)} {rs : List K}
    (aligned : List.Forall₂ (fun a r => r ∈ Set.Icc (a.1 : K) (a.2 : K)) boxes rs)
    (L : K[X] →ₗ[K] K) (d : K) (body : K[X]) (positive : Bool)
    (corners : ∀ v ∈ factorCorners boxes,
      0 < signedValue positive (L (body * (v.map (fun r : ℤ => portFactor d (r : K))).prod))) :
    0 < signedValue positive (L (body * (rs.map (portFactor d)).prod)) := by
  induction aligned generalizing body with
  | nil => exact corners [] (by simp [factorCorners])
  | @cons a r bs rs hmem _ ih =>
    obtain ⟨t, ht, hrt⟩ := exists_unit_mix hmem
    have lower : 0 < signedValue positive
        (L ((body * portFactor d (a.1 : K)) * (rs.map (portFactor d)).prod)) := by
      apply ih (body * portFactor d (a.1 : K))
      intro v hv
      have hm : a.1 :: v ∈ factorCorners (a :: bs) := List.mem_append_left _
        (List.mem_map.mpr ⟨v, hv, rfl⟩)
      simpa only [List.map_cons, List.prod_cons, mul_assoc] using corners _ hm
    have upper : 0 < signedValue positive
        (L ((body * portFactor d (a.2 : K)) * (rs.map (portFactor d)).prod)) := by
      apply ih (body * portFactor d (a.2 : K))
      intro v hv
      have hm : a.2 :: v ∈ factorCorners (a :: bs) := List.mem_append_right _
        (List.mem_map.mpr ⟨v, hv, rfl⟩)
      simpa only [List.map_cons, List.prod_cons, mul_assoc] using corners _ hm
    have aff : portFactor d r = (1 - t) • portFactor d (a.1 : K) + t • portFactor d (a.2 : K) := by
      rw [hrt]
      simp only [portFactor, mix, Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_one]
      ring
    change 0 < signedValue positive (L (body * (portFactor d r * (rs.map (portFactor d)).prod)))
    rw [aff]
    simpa only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, map_add, map_smul, smul_eq_mul,
      mix, mul_assoc] using signedMix positive ht.1 ht.2 lower upper

theorem boxPortOK_sound {positive : Bool} {e : ℕ} {l u : ℤ} {boxes : List (ℤ × ℤ)}
    (ok : boxPortOK positive e l u boxes = true) {d : K} (hd : d ∈ Set.Icc (l : K) (u : K))
    {rs : List K} (aligned : List.Forall₂ (fun a r => r ∈ Set.Icc (a.1 : K) (a.2 : K)) boxes rs) :
    0 < signedValue positive (formalPort e d rs) := by
  apply product_corners aligned unitFunctional d (X ^ e) positive
  intro v hv
  have h := vertexPortOK_sound (List.all_eq_true.mp ok v hv) hd
  rw [formalPort, List.map_map] at h
  exact h

end RKCert.ReviewedNative.PolynomialCertificate
