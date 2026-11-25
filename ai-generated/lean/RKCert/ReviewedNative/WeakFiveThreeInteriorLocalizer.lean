module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorNormalized
public import RKCert.ReviewedNative.PolynomialCertificateAffinePencil
public import Mathlib.Data.Rat.Cast.Order

import Mathlib.Tactic.Ring

@[expose] public section

/-! # Exact affine localizers for all six paid three-interior ports

The six rows follow the released rational table's convention, including
the negated original test at RH. Every coordinate is an exact affine
ratio, not a sample estimate or an assumed convergence property.
-/
namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.OrderedPolynomialSignStrips
open RKCert.ReviewedNative.PolynomialCertificate
open scoped Polynomial BigOperators

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

inductive ThreeInteriorPort
  | l1 | l2 | la | r1 | r2 | rh
  deriving DecidableEq

def ThreeInteriorPort.extra : ThreeInteriorPort → Bool
  | .la | .rh => true
  | _ => false

def ThreeInteriorPort.side : ThreeInteriorPort → Bool
  | .l1 | .l2 | .la => false
  | _ => true

def ThreeInteriorPort.exponent : ThreeInteriorPort → ℕ
  | .l2 | .r2 => 2
  | _ => 1

def ThreeInteriorPort.count : ThreeInteriorPort → ℕ
  | .la | .rh => 4
  | _ => 3

def threeInteriorLeftScale (s d : K) : K := s+(1-s)*d
def threeInteriorLeftGamma (s d : K) : K := (1-s)*d/threeInteriorLeftScale s d
def threeInteriorRightGamma (s d : K) : K := (1-s)*(1-d)
def threeInteriorLeftRoot (d x : K) : K := x/d
def threeInteriorRightRoot (d x : K) : K := (x-d)/(1-d)

def threeInteriorLocalizerArgs (p : ThreeInteriorPort) (s : K) (r : Fin 3 → K)
    (m : Fin 4 → K) : Fin (p.count+1) → K :=
  match p with
  | .l1 | .l2 => Fin.cons (threeInteriorLeftGamma s (m 0))
      (fun j => threeInteriorLeftRoot (m 0) (r j))
  | .la => Fin.cons (threeInteriorLeftGamma s (m 1))
      (Fin.cons (threeInteriorLeftRoot (m 1) (m 0))
        (fun j => threeInteriorLeftRoot (m 1) (r j)))
  | .r1 | .r2 => Fin.cons (threeInteriorRightGamma s (m 3))
      (fun j => threeInteriorRightRoot (m 3) (r j))
  | .rh => Fin.cons (threeInteriorRightGamma s (m 2))
      (Fin.cons (threeInteriorRightRoot (m 2) (m 3))
        (fun j => threeInteriorRightRoot (m 2) (r j)))

noncomputable section

def threeInteriorCap : Bool → K[X]
  | false => X
  | true => 1-X

/-- Coordinate 0 is the affine density parameter gamma; the remaining
coordinates are the three root ratios and, for LA/RH, the extra ratio. -/
def threeInteriorLocalizerPencil {n : ℕ} (right : Bool) (p : ℕ)
    (y : Fin (n+1) → K) : K :=
  let g : Fin (n+1) → K[X] := Fin.cons 1 (fun _ => X)
  let h : Fin (n+1) → K[X] := Fin.cons (X-1) (fun _ => -1)
  integral 0 1 (threeInteriorCap right ^ p * ∏ i, (g i+C (y i)*h i))

theorem threeInteriorLocalizerPencil_affine {n : ℕ} (right : Bool) (p : ℕ) :
    SeparatelyAffine (threeInteriorLocalizerPencil (K := K) (n := n) right p) := by
  unfold threeInteriorLocalizerPencil
  exact separatelyAffine_polynomial_pencil _ _ _ _

theorem threeInteriorLocalizerPencil_cons {n : ℕ} (right : Bool) (p : ℕ) (γ : K)
    (a : Fin n → K) :
    threeInteriorLocalizerPencil right p (Fin.cons γ a) = integral 0 1
      (threeInteriorCap right ^ p * (threeInteriorResidual (1-γ) * indexedHull a Finset.univ)) := by
  unfold threeInteriorLocalizerPencil
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_neg, mul_one, ← sub_eq_add_neg]
  have line : (1 : K[X])+C γ*(X-1) = threeInteriorResidual (1-γ) := by
    simp only [threeInteriorResidual, sub_sub_cancel, C_sub, C_1]
    ring
  rw [line] <;> rfl

def threeInteriorLocalizer (p : ThreeInteriorPort) (y : Fin (p.count+1) → K) : K :=
  threeInteriorLocalizerPencil p.side p.exponent y

def threeInteriorSigned : Bool → K → Prop
  | false, x => x < 0
  | true, x => 0 < x

/-- This is the reusable ordered-field sign/localizer certificate consumer.
The interval and vertices are supplied by any exact receipt, including
the existing released rectangular certificate. -/
theorem threeInteriorLocalizer_signed_box (p : ThreeInteriorPort) (positive : Bool)
    {l u y : Fin (p.count+1) → K} (bounds : ∀ j, y j ∈ Set.Icc (l j) (u j))
    (vertices : ∀ a : Fin (p.count+1) → Bool,
      threeInteriorSigned positive (threeInteriorLocalizer p (vertex l u a))) :
    threeInteriorSigned positive (threeInteriorLocalizer p y) := by
  have aff : SeparatelyAffine (threeInteriorLocalizer (K := K) p) :=
    threeInteriorLocalizerPencil_affine p.side p.exponent
  cases positive
  · exact box_of_vertices aff bounds (mixClosed_strictUpper 0) vertices
  · exact box_of_vertices aff bounds (mixClosed_strictLower 0) vertices

private theorem rational_hull_map {n : ℕ} (a : Fin n → ℚ) :
    (indexedHull a Finset.univ).map (Rat.castHom K) =
      indexedHull (fun i => (a i : K)) Finset.univ := by
  unfold indexedHull
  change Polynomial.mapRingHom (Rat.castHom K) (∏ i, (X-C (a i))) =
    ∏ i, (X-C (a i : K))
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Polynomial.coe_mapRingHom, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] <;> rfl

private theorem rational_localizer_cons {n : ℕ} (right : Bool) (p : ℕ) (γ : ℚ)
    (a : Fin n → ℚ) :
    threeInteriorLocalizerPencil right p (Fin.cons (γ : K) (fun i => (a i : K))) =
      ((threeInteriorLocalizerPencil right p (Fin.cons γ a) : ℚ) : K) := by
  let f : ℚ →+* K := Rat.castHom K
  rw [threeInteriorLocalizerPencil_cons, threeInteriorLocalizerPencil_cons]
  change integral 0 1 (threeInteriorCap right ^ p *
    (threeInteriorResidual (1-f γ) * indexedHull (fun i => f (a i)) Finset.univ)) =
    f (integral 0 1
      (threeInteriorCap right ^ p * (threeInteriorResidual (1-γ) * indexedHull a Finset.univ)))
  rw [← integral_along_field f, map_zero, map_one, Polynomial.map_mul, Polynomial.map_mul,
    Polynomial.map_pow]
  have cap : (threeInteriorCap right : ℚ[X]).map f = threeInteriorCap right := by
    cases right <;> simp [threeInteriorCap]
  have line : (threeInteriorResidual (1-γ)).map f = threeInteriorResidual (1-f γ) := by
    simp only [threeInteriorResidual, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, Polynomial.map_sub, Polynomial.map_one, map_sub, map_one]
  rw [cap, line, rational_hull_map] <;> rfl

/-- The table needs to establish its corner signs only over rationals. -/
theorem threeInteriorLocalizer_ratCast (p : ThreeInteriorPort) (y : Fin (p.count+1) → ℚ) :
    threeInteriorLocalizer p (fun j => (y j : K)) = ((threeInteriorLocalizer p y : ℚ) : K) := by
  have eq₀ : Fin.cons (y 0) (Fin.tail y) = y := Fin.cons_self_tail y
  have eq₁ : Fin.cons (y 0 : K) (fun j => (Fin.tail y j : K)) = (fun j => (y j : K)) := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · rfl
  simpa only [eq₀, eq₁, threeInteriorLocalizer] using
    rational_localizer_cons (K := K) p.side p.exponent (y 0) (Fin.tail y)

theorem threeInteriorLocalizer_signed_rat_box (p : ThreeInteriorPort) (positive : Bool)
    {l u : Fin (p.count+1) → ℚ} {y : Fin (p.count+1) → K}
    (bounds : ∀ j, y j ∈ Set.Icc (l j : K) (u j : K))
    (corners : ∀ a : Fin (p.count+1) → Bool,
      threeInteriorSigned positive (threeInteriorLocalizer p (vertex l u a))) :
    threeInteriorSigned positive (threeInteriorLocalizer p y) := by
  refine threeInteriorLocalizer_signed_box p positive bounds ?_
  intro a
  have v : (vertex (fun j => (l j : K)) (fun j => (u j : K)) a) =
      (fun j => (Rat.castHom K) (vertex l u a j)) := by
    funext j
    unfold vertex
    cases a j <;> rfl
  rw [v]
  let vr : Fin (p.count + 1) → ℚ := vertex l u a
  change threeInteriorSigned positive (threeInteriorLocalizer p (fun j => (vr j : K)))
  rw [threeInteriorLocalizer_ratCast]
  cases positive
  · exact Rat.cast_lt_zero.mpr (corners a)
  · exact Rat.cast_pos.mpr (corners a)

private theorem left_c_pos {s d : K} (ss : s ∈ Set.Ico 0 1) (d0 : 0 < d) :
    0 < threeInteriorLeftScale s d :=
  add_pos_of_nonneg_of_pos ss.1 (mul_pos (sub_pos.mpr ss.2) d0)

private theorem left_line {s d : K} (c0 : 0 < threeInteriorLeftScale s d) :
    (threeInteriorResidual s).comp (C d*X) =
      C (threeInteriorLeftScale s d)*threeInteriorResidual (1-threeInteriorLeftGamma s d) := by
  let c := threeInteriorLeftScale s d
  let γ := threeInteriorLeftGamma s d
  have gc : c*γ = (1-s)*d := by
    change c*((1-s)*d/c) = (1-s)*d
    rw [mul_comm, div_mul_cancel₀ _ c0.ne']
  have cc : c*(1-γ) = s := by
    calc
      c*(1-γ) = c-c*γ := by ring
      _ = s := by rw [gc]; unfold c threeInteriorLeftScale; ring
  have t₀ : C c*C (1-γ) = C s := by rw [← C_mul, cc]
  have t₁ : C c*C γ = C ((1-s)*d) := by rw [← C_mul, gc]
  have t₂ : C (1-s)*C d = C ((1-s)*d) := by rw [C_mul]
  change (threeInteriorResidual s).comp (C d*X) =
    C c * threeInteriorResidual (1-γ)
  simp only [threeInteriorResidual, add_comp, mul_comp, C_comp, X_comp, mul_add,
    ← mul_assoc, sub_sub_cancel, t₀, t₁, t₂]

private theorem right_line (s d : K) :
    (threeInteriorResidual s).comp (C (1-d)*X+C d) =
      threeInteriorResidual (1-threeInteriorRightGamma s d) := by
  have e : 1-threeInteriorRightGamma s d = s+(1-s)*d := by
    unfold threeInteriorRightGamma
    ring
  simp only [threeInteriorResidual, add_comp, C_comp, mul_comp, X_comp,
    mul_add, ← mul_assoc, ← C_mul, sub_sub_cancel]
  rw [e, C_add]
  unfold threeInteriorRightGamma
  ring

private theorem left_factor {d x : K} (dn : d ≠ 0) :
    (X-C x).comp (C d*X) = C d*(X-C (threeInteriorLeftRoot d x)) := by
  have h : d*threeInteriorLeftRoot d x = x := by
    unfold threeInteriorLeftRoot
    rw [mul_comm, div_mul_cancel₀ _ dn]
  simp only [sub_comp, X_comp, C_comp, mul_sub, ← C_mul, h]

private theorem right_factor {d x : K} (dn : 1-d ≠ 0) :
    (X-C x).comp (C (1-d)*X+C d) = C (1-d)*(X-C (threeInteriorRightRoot d x)) := by
  have h : (1-d)*threeInteriorRightRoot d x = x-d := by
    unfold threeInteriorRightRoot
    rw [mul_comm, div_mul_cancel₀ _ dn]
  simp only [sub_comp, X_comp, C_comp, mul_sub, ← C_mul, h]
  simp only [C_sub] <;> ring

private theorem right_cap_comp (d : K) :
    (1-X : K[X]).comp (C (1-d)*X+C d) = C (1-d)*(1-X) := by
  simp only [sub_comp, one_comp, X_comp, C_sub, C_1]
  ring

private theorem left_profile_comp {s d : K} (r : Fin 3 → K)
    (c0 : 0 < threeInteriorLeftScale s d) (dn : d ≠ 0) :
    (threeInteriorProfile s r).comp (C d*X) =
      (C (threeInteriorLeftScale s d)*C d^3) *
        threeInteriorProfile (1-threeInteriorLeftGamma s d) (fun i => threeInteriorLeftRoot d (r i)) := by
  simp only [threeInteriorProfile, threeInterior_hull_three, mul_comp,
    left_line c0, left_factor dn]
  ring

private theorem right_profile_comp {s d : K} (r : Fin 3 → K) (dn : 1-d ≠ 0) :
    (threeInteriorProfile s r).comp (C (1-d)*X+C d) =
      C (1-d)^3 *
        threeInteriorProfile (1-threeInteriorRightGamma s d) (fun i => threeInteriorRightRoot d (r i)) := by
  simp only [threeInteriorProfile, threeInterior_hull_three, mul_comp,
    right_line, right_factor dn]
  ring

private theorem left_port_rescale {s d v : K} (r : Fin 3 → K) (p : ℕ) {R V : K[X]}
    (c0 : 0 < threeInteriorLeftScale s d) (dn : d ≠ 0)
    (shape : R.comp (C d*X) = C v*V) :
    integral 0 d (X^p*R*threeInteriorProfile s r) =
      d*(d^p*v*(threeInteriorLeftScale s d*d^3)) * integral 0 1
        (X^p*V*threeInteriorProfile
          (1-threeInteriorLeftGamma s d) (fun i => threeInteriorLeftRoot d (r i))) := by
  rw [integral_affine, sub_zero, C_0, add_zero]
  have comp_eq :
      (X^p*R*threeInteriorProfile s r).comp (C d*X) =
        C (d^p*v*(threeInteriorLeftScale s d*d^3)) *
          (X^p*V*threeInteriorProfile
            (1-threeInteriorLeftGamma s d) (fun i => threeInteriorLeftRoot d (r i))) := by
    simp only [mul_comp, pow_comp, X_comp, shape, left_profile_comp r c0 dn,
      mul_pow, C_mul, C_pow]
    ring
  rw [comp_eq, threeInterior_integral_C_mul]
  ring

private theorem right_port_rescale {s d v : K} (r : Fin 3 → K) (p : ℕ) {R V : K[X]}
    (dn : 1-d ≠ 0) (shape : R.comp (C (1-d)*X+C d) = C v*V) :
    integral d 1 ((1-X)^p*R*threeInteriorProfile s r) =
      (1-d)*((1-d)^p*v*(1-d)^3) * integral 0 1
        ((1-X)^p*V*threeInteriorProfile
          (1-threeInteriorRightGamma s d) (fun i => threeInteriorRightRoot d (r i))) := by
  rw [integral_affine]
  have comp_eq :
      (((1-X)^p)*R*threeInteriorProfile s r).comp (C (1-d)*X+C d) =
        C ((1-d)^p*v*(1-d)^3) * (((1-X)^p)*V*threeInteriorProfile
          (1-threeInteriorRightGamma s d) (fun i => threeInteriorRightRoot d (r i))) := by
    simp only [mul_comp, pow_comp, right_cap_comp, shape, right_profile_comp r dn, mul_pow,
      C_mul, C_pow]
    ring
  rw [comp_eq, threeInterior_integral_C_mul]
  ring

private theorem left_port_zero {s d v : K} (r : Fin 3 → K) (p : ℕ) {R V : K[X]}
    (ss : s ∈ Set.Ico 0 1) (d0 : 0 < d) (v0 : v ≠ 0)
    (shape : R.comp (C d*X) = C v*V)
    (paid : integral 0 d (X^p*R*threeInteriorProfile s r) = 0) :
    integral 0 1 (X^p*V*threeInteriorProfile
      (1-threeInteriorLeftGamma s d) (fun i => threeInteriorLeftRoot d (r i))) = 0 := by
  have c0 := left_c_pos ss d0
  rw [left_port_rescale r p c0 d0.ne' shape] at paid
  exact (mul_eq_zero.mp paid).resolve_left
    (mul_ne_zero d0.ne' (mul_ne_zero (mul_ne_zero (pow_ne_zero _ d0.ne') v0)
      (mul_ne_zero c0.ne' (pow_ne_zero _ d0.ne'))))

private theorem right_port_zero {s d v : K} (r : Fin 3 → K) (p : ℕ) {R V : K[X]}
    (d1 : d < 1) (v0 : v ≠ 0)
    (shape : R.comp (C (1-d)*X+C d) = C v*V)
    (paid : integral d 1 ((1-X)^p*R*threeInteriorProfile s r) = 0) :
    integral 0 1 ((1-X)^p*V*threeInteriorProfile
      (1-threeInteriorRightGamma s d) (fun i => threeInteriorRightRoot d (r i))) = 0 := by
  have dn := (sub_pos.mpr d1).ne'
  rw [right_port_rescale r p dn shape] at paid
  exact (mul_eq_zero.mp paid).resolve_left
    (mul_ne_zero dn (mul_ne_zero (mul_ne_zero (pow_ne_zero _ dn) v0) (pow_ne_zero _ dn)))

private theorem hull_cons {n : ℕ} (a : K) (r : Fin n → K) :
    indexedHull (Fin.cons a r) Finset.univ = (X-C a)*indexedHull r Finset.univ := by
  simp only [indexedHull, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- All six exact localizers vanish on the actual normalized packet. -/
theorem ThreeInteriorNormalized.localizer_zero {s : K} {r : Fin 3 → K} {m : Fin 4 → K}
    (H : ThreeInteriorNormalized s r m) (p : ThreeInteriorPort) :
    threeInteriorLocalizer p (threeInteriorLocalizerArgs p s r m) = 0 := by
  let q := threeInteriorProfile s r
  have LS (d : K) : (1 : K[X]).comp (C d*X) = C (1:K)*1 := by simp
  have RS (d : K) : (1 : K[X]).comp (C (1-d)*X+C d) = C (1:K)*1 := by simp
  cases p
  · have paid : integral 0 (m 0) (X^1*1*q) = 0 := by simpa only [pow_one, mul_one] using H.stops.l1
    change threeInteriorLocalizerPencil false 1 (Fin.cons
      (threeInteriorLeftGamma s (m 0))
      (fun i : Fin 3 => threeInteriorLeftRoot (m 0) (r i))) = 0
    rw [threeInteriorLocalizerPencil_cons]
    have hz := left_port_zero r 1 H.parameter (H.markInside 0).1 one_ne_zero (LS (m 0)) paid
    simpa only [threeInteriorCap, threeInteriorProfile, mul_one] using hz
  · have paid : integral 0 (m 0) (X^2*1*q) = 0 := by simpa only [mul_one] using H.stops.l2
    change threeInteriorLocalizerPencil false 2 (Fin.cons
      (threeInteriorLeftGamma s (m 0))
      (fun i : Fin 3 => threeInteriorLeftRoot (m 0) (r i))) = 0
    rw [threeInteriorLocalizerPencil_cons]
    have hz := left_port_zero r 2 H.parameter (H.markInside 0).1 one_ne_zero (LS (m 0)) paid
    simpa only [threeInteriorCap, threeInteriorProfile, mul_one] using hz
  · have d0 := (H.markInside 1).1
    have paid : integral 0 (m 1) (X^1*(X-C (m 0))*q) = 0 := by
      simpa only [pow_one] using H.stops.la
    have z := left_port_zero r 1 H.parameter d0 d0.ne' (left_factor (x := m 0) d0.ne') paid
    change threeInteriorLocalizerPencil false 1 (Fin.cons (threeInteriorLeftGamma s (m 1))
      (Fin.cons (threeInteriorLeftRoot (m 1) (m 0))
        (fun i : Fin 3 => threeInteriorLeftRoot (m 1) (r i)))) = 0
    rw [threeInteriorLocalizerPencil_cons, hull_cons]
    refine (congrArg (fun P : K[X] => integral 0 1 P) ?_).trans z
    unfold threeInteriorCap threeInteriorProfile
    ring
  · have paid : integral (m 3) 1 ((1-X)^1*1*q) = 0 := by simpa only [pow_one, mul_one] using H.stops.r1
    change threeInteriorLocalizerPencil true 1 (Fin.cons
      (threeInteriorRightGamma s (m 3))
      (fun i : Fin 3 => threeInteriorRightRoot (m 3) (r i))) = 0
    rw [threeInteriorLocalizerPencil_cons]
    have hz := right_port_zero r 1 (H.markInside 3).2 one_ne_zero (RS (m 3)) paid
    simpa only [threeInteriorCap, threeInteriorProfile, mul_one] using hz
  · have paid : integral (m 3) 1 ((1-X)^2*1*q) = 0 := by simpa only [mul_one] using H.stops.r2
    change threeInteriorLocalizerPencil true 2 (Fin.cons
      (threeInteriorRightGamma s (m 3))
      (fun i : Fin 3 => threeInteriorRightRoot (m 3) (r i))) = 0
    rw [threeInteriorLocalizerPencil_cons]
    have hz := right_port_zero r 2 (H.markInside 3).2 one_ne_zero (RS (m 3)) paid
    simpa only [threeInteriorCap, threeInteriorProfile, mul_one] using hz
  · have d1 := (H.markInside 2).2
    have dn := (sub_pos.mpr d1).ne'
    have paid : integral (m 2) 1 ((1-X)^1*(X-C (m 3))*q) = 0 := by
      rw [show (1-X)^1*(X-C (m 3))*q = -((1-X)*(C (m 3)-X)*q) by ring,
        map_neg, H.stops.rh, neg_zero]
    have z := right_port_zero r 1 d1 dn (right_factor (x := m 3) dn) paid
    change threeInteriorLocalizerPencil true 1 (Fin.cons (threeInteriorRightGamma s (m 2))
      (Fin.cons (threeInteriorRightRoot (m 2) (m 3))
        (fun i : Fin 3 => threeInteriorRightRoot (m 2) (r i)))) = 0
    rw [threeInteriorLocalizerPencil_cons, hull_cons]
    refine (congrArg (fun P : K[X] => integral 0 1 P) ?_).trans z
    unfold threeInteriorCap threeInteriorProfile
    ring

end
end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
