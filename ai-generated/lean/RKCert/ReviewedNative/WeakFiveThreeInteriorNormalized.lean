module

public import RKCert.ReviewedNative.ERKOrder16WeakFiveRemainingScalarCases
public import RKCert.ReviewedNative.WeakFivePrimitiveBalance
public import Mathlib.Data.Fin.Rev
public import Mathlib.Algebra.BigOperators.Fin

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Literal weak-five three-interior packet in the left-residual orientation

Only the four nonorigin marks are transported. In particular reflection is
valid at the seam where the old q(1), and hence the new q(0), vanishes.
-/
namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.WeakFive16 RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.OrderedRootGapSaturation
open RKCert.ReviewedNative.OrderedPolynomialSignStrips
open scoped Polynomial BigOperators

universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

noncomputable section

/-- Local primitives at the actual physical labels `u,a,h,z`, not sorted labels. -/
structure ThreeInteriorStops (q : K[X]) (m : Fin 4 → K) : Prop where
  l1 : integral 0 (m 0) (X*q) = 0
  l2 : integral 0 (m 0) (X^2*q) = 0
  la : integral 0 (m 1) (X*(X-C (m 0))*q) = 0
  r1 : integral (m 3) 1 ((1-X)*q) = 0
  r2 : integral (m 3) 1 ((1-X)^2*q) = 0
  rh : integral (m 2) 1 ((1-X)*(C (m 3)-X)*q) = 0

def threeInteriorResidual (s : K) : K[X] := C s + C (1-s)*X

def threeInteriorProfile (s : K) (r : Fin 3 → K) : K[X] :=
  threeInteriorResidual s * indexedHull r Finset.univ

structure ThreeInteriorNormalized (s : K) (r : Fin 3 → K) (m : Fin 4 → K) : Prop where
  parameter : s ∈ Set.Ico 0 1
  rootOrder : StrictMono r
  rootInside : ∀ i, r i ∈ Set.Ioo 0 1
  markInside : ∀ j, m j ∈ Set.Ioo 0 1
  markDistinct : Function.Injective m
  markOffRoot : ∀ j, (threeInteriorProfile s r).eval (m j) ≠ 0
  stops : ThreeInteriorStops (threeInteriorProfile s r) m
  global : PaidSix (threeInteriorProfile s r) (m 0) (m 1) (m 2) (m 3)

def threeInteriorMirror {n : ℕ} (v : Fin n → K) (i : Fin n) : K := 1-v i.rev

theorem threeInterior_hull_three (r : Fin 3 → K) :
    indexedHull r Finset.univ = (X-C (r 0))*(X-C (r 1))*(X-C (r 2)) := by
  rw [indexedHull, Fin.prod_univ_three]

private theorem mirror_inside {n : ℕ} {v : Fin n → K}
    (h : ∀ i, v i ∈ Set.Ioo 0 1) (i : Fin n) :
    threeInteriorMirror v i ∈ Set.Ioo 0 1 := by
  change 0 < 1-v i.rev ∧ 1-v i.rev < 1
  exact ⟨sub_pos.mpr (h i.rev).2, by linarith only [(h i.rev).1]⟩

private theorem mirror_injective {n : ℕ} {v : Fin n → K} (h : Function.Injective v) :
    Function.Injective (threeInteriorMirror v) := by
  intro i j e
  change 1-v i.rev = 1-v j.rev at e
  exact Fin.rev_injective (h (sub_right_inj.mp e))

private theorem mirror_strictMono {n : ℕ} {v : Fin n → K} (h : StrictMono v) :
    StrictMono (threeInteriorMirror v) := by
  intro i j e
  change 1-v i.rev < 1-v j.rev
  exact sub_lt_sub_left (h (Fin.rev_lt_rev.mpr e)) 1

private theorem reflect_twice (P : K[X]) : (P.comp (1-X)).comp (1-X) = P := by
  rw [comp_assoc, show (1-X : K[X]).comp (1-X) = X by
    simp only [sub_comp, one_comp, X_comp, sub_sub_cancel], comp_X]

private theorem reflect_right (P : K[X]) (x : K) :
    integral (1-x) 1 (P.comp (1-X)) = integral 0 x P := by
  calc
    _ = integral 0 x ((P.comp (1-X)).comp (1-X)) := by
      simpa only [sub_sub_cancel] using (integral_reflect (P.comp (1-X)) (1-x)).symm
    _ = integral 0 x P := congrArg (fun Q : K[X] => integral 0 x Q) (reflect_twice P)

private theorem ThreeInteriorStops.reflect {P : K[X]} {m : Fin 4 → K}
    (H : ThreeInteriorStops P m) :
    ThreeInteriorStops (P.comp (1-X)) (threeInteriorMirror m) := by
  constructor
  · change integral 0 (1-m 3) (X*P.comp (1-X)) = 0
    simpa only [mul_comp, sub_comp, one_comp, X_comp, sub_sub_cancel] using
      (integral_reflect ((1-X)*P) (m 3)).trans H.r1
  · change integral 0 (1-m 3) (X^2*P.comp (1-X)) = 0
    simpa only [mul_comp, pow_comp, sub_comp, one_comp, X_comp, sub_sub_cancel] using
      (integral_reflect ((1-X)^2*P) (m 3)).trans H.r2
  · change integral 0 (1-m 2) (X*(X-C (1-m 3))*P.comp (1-X)) = 0
    have e : ((1-X)*(C (m 3)-X)*P).comp (1-X) =
        X*(X-C (1-m 3))*P.comp (1-X) := by
      simp only [mul_comp, sub_comp, X_comp, C_comp, one_comp, map_sub, map_one]
      ring
    simpa only [e] using (integral_reflect ((1-X)*(C (m 3)-X)*P) (m 2)).trans H.rh
  · change integral (1-m 0) 1 ((1-X)*P.comp (1-X)) = 0
    simpa only [mul_comp, X_comp] using (reflect_right (X*P) (m 0)).trans H.l1
  · change integral (1-m 0) 1 ((1-X)^2*P.comp (1-X)) = 0
    simpa only [mul_comp, pow_comp, X_comp] using (reflect_right (X^2*P) (m 0)).trans H.l2
  · change integral (1-m 1) 1 ((1-X)*(C (1-m 0)-X)*P.comp (1-X)) = 0
    have e : (X*(X-C (m 0))*P).comp (1-X) =
        (1-X)*(C (1-m 0)-X)*P.comp (1-X) := by
      simp only [mul_comp, sub_comp, X_comp, C_comp, map_sub, map_one]
      ring
    simpa only [e] using (reflect_right (X*(X-C (m 0))*P) (m 1)).trans H.la

theorem threeInterior_integral_C_mul (a b k : K) (P : K[X]) :
    integral a b (C k*P) = k*integral a b P := by
  simpa only [smul_eq_C_mul, smul_eq_mul] using (integral a b).map_smul k P

private theorem descale_test {P q : K[X]} {k : K} (qP : q = C k*P) (hn : k ≠ 0)
    {a b : K} (W : K[X]) (paid : integral a b (W*q) = 0) : integral a b (W*P) = 0 := by
  rw [qP, show W*(C k*P) = C k*(W*P) by ring, threeInterior_integral_C_mul] at paid
  exact (mul_eq_zero.mp paid).resolve_left hn

private theorem ThreeInteriorStops.descale {P q : K[X]} {k : K} {m : Fin 4 → K}
    (H : ThreeInteriorStops q m) (qP : q = C k*P) (hn : k ≠ 0) :
    ThreeInteriorStops P m :=
  ⟨descale_test qP hn _ H.l1, descale_test qP hn _ H.l2, descale_test qP hn _ H.la,
    descale_test qP hn _ H.r1, descale_test qP hn _ H.r2, descale_test qP hn _ H.rh⟩

private theorem descale_paid {P q : K[X]} {k : K} {m : Fin 4 → K}
    (H : PaidSix q (m 0) (m 1) (m 2) (m 3)) (qP : q = C k*P) (hn : k ≠ 0) :
    PaidSix P (m 0) (m 1) (m 2) (m 3) := by
  intro R rd
  have z := H R rd
  rw [qP, show X*(1-X)*((C k*P)*rawFourHull (m 0) (m 1) (m 2) (m 3))*R =
      C k*(X*(1-X)*(P*rawFourHull (m 0) (m 1) (m 2) (m 3))*R) by ring,
    threeInterior_integral_C_mul] at z
  exact (mul_eq_zero.mp z).resolve_left hn

private theorem reflect_factor {P : K[X]} {k e : K} {r : Fin 3 → K}
    (h : P = C k*((X-C e)*indexedHull r Finset.univ)) :
    P.comp (1-X) =
      C k*((X-C (1-e))*indexedHull (threeInteriorMirror r) Finset.univ) := by
  have h₀ : threeInteriorMirror r 0 = 1-r 2 := rfl
  have h₁ : threeInteriorMirror r 1 = 1-r 1 := rfl
  have h₂ : threeInteriorMirror r 2 = 1-r 0 := rfl
  rw [h, threeInterior_hull_three r, threeInterior_hull_three (threeInteriorMirror r)]
  simp only [mul_comp, sub_comp, X_comp, C_comp, h₀, h₁, h₂, C_sub, C_1]
  ring

private theorem normalize_left {P : K[X]} {r : Fin 3 → K} {m : Fin 4 → K} {k e : K}
    (en : e ≤ 0) (kn : k ≠ 0)
    (factor : P = C k*((X-C e)*indexedHull r Finset.univ))
    (sorted : StrictMono r) (inside : ∀ i, r i ∈ Set.Ioo 0 1)
    (marks : ∀ j, m j ∈ Set.Ioo 0 1) (distinct : Function.Injective m)
    (off : ∀ j, P.eval (m j) ≠ 0) (stops : ThreeInteriorStops P m)
    (paid : PaidSix P (m 0) (m 1) (m 2) (m 3)) :
    ∃ s t : K, t ≠ 0 ∧ P = C t*threeInteriorProfile s r ∧ ThreeInteriorNormalized s r m := by
  let d : K := 1-e
  let s : K := (-e)/d
  have dpos : 0 < d := by dsimp [d]; linarith only [en]
  have ds : d*s = -e := by
    dsimp only [s]
    rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt dpos)]
  have dl : d*(1-s) = 1 := by
    have f : d*(1-s) = d-d*s := by ring
    rw [f, ds]
    dsimp only [d]
    ring
  have shape : C d*threeInteriorResidual s = X-C e := by
    rw [threeInteriorResidual, mul_add, ← mul_assoc, ← C_mul, ds, ← C_mul, dl, C_1,
      one_mul, C_neg]
    ring
  have hn : k*d ≠ 0 := mul_ne_zero kn (ne_of_gt dpos)
  have form : P = C (k*d)*threeInteriorProfile s r := by
    rw [factor, threeInteriorProfile, C_mul, ← shape]
    ring
  refine ⟨s, k*d, hn, form, ⟨⟨div_nonneg (neg_nonneg.mpr en) dpos.le, ?_⟩,
    sorted, inside, marks, distinct, ?_, stops.descale form hn, descale_paid paid form hn⟩⟩
  · change (-e)/d < 1
    apply (div_lt_iff₀ dpos).2
    dsimp only [d]
    linarith
  · intro j z
    apply off j
    rw [form, eval_mul, z, mul_zero]

private abbrev interiorMarks (c : Fin 5 → K) : Fin 4 → K := fun j => c j.succ

private theorem stops_of_moments {P Z : K[X]} {c : Fin 5 → K} (H : Moments P Z c) :
    ThreeInteriorStops P (interiorMarks c) :=
  ⟨H.forwardFirst, H.forwardSecond, H.forwardInner, H.reverseFirst, H.reverseSecond, H.reverseInner⟩

/- Keep the degree-five paid equation at its exact native source
coordinates before introducing aliases or the ordered extension. This
prevents unification under the integral while the clocks are unknown. -/
private theorem interior_paid_of_moments {P Z : K[X]} {d : Fin 5 → K}
    (H : Moments P Z d) :
    PaidSix P ((interiorMarks d) 0) ((interiorMarks d) 1)
      ((interiorMarks d) 2) ((interiorMarks d) 3) := by
  have paidNative : PaidSix P (d 1) (d 2) (d 3) (d 4) :=
    paidSix_of_actual_moments (K := K) (q := P) (Z := Z) (c := d) H
  change PaidSix P (d 1) (d 2) (d 3) (d 4)
  exact paidNative

private theorem interior_reflected_paid_of_moments {P Z : K[X]} {d : Fin 5 → K}
    (H : Moments P Z d) :
    PaidSix (P.comp (1-X))
      ((threeInteriorMirror (interiorMarks d)) 0)
      ((threeInteriorMirror (interiorMarks d)) 1)
      ((threeInteriorMirror (interiorMarks d)) 2)
      ((threeInteriorMirror (interiorMarks d)) 3) := by
  have paidNative : PaidSix (P.comp (1-X)) (1-d 4) (1-d 3) (1-d 2) (1-d 1) :=
    reflected_paidSix (K := K) (q := P) (Z := Z) (c := d) H
  change PaidSix (P.comp (1-X)) (1-d 4) (1-d 3) (1-d 2) (1-d 1)
  exact paidNative

/-- The unreflected branch is assembled entirely over its already fixed
coefficient field. All physical arguments of normalize_left are fixed
before inserting the paid primitive. -/
private theorem normalize_unreflected_layout {P Z : K[X]} {d : Fin 5 → K}
    {r : Fin 3 → K} {e : K} (H : Moments P Z d) (inside : AllFourMarksInterior d)
    (L : ThreeChangeLayout P r e) (he : e ≤ 0) :
    ∃ s t : K, t ≠ 0 ∧ P = C t*threeInteriorProfile s r ∧
      ThreeInteriorNormalized s r (interiorMarks d) := by
  let m : Fin 4 → K := interiorMarks d
  have lead : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr H.qNonzero
  have fac : P = C P.leadingCoeff*((X-C e)*indexedHull r Finset.univ) := L.factor
  have ord : StrictMono r := L.sorted
  have unit : ∀ i : Fin 3, r i ∈ Set.Ioo 0 1 := L.unit
  have marks : ∀ j : Fin 4, m j ∈ Set.Ioo 0 1 := inside
  have inj : Function.Injective m := H.clockSimple.comp (Fin.succ_injective 4)
  have off (j : Fin 4) : P.eval (m j) ≠ 0 := (H.active j.succ).2
  have stops : ThreeInteriorStops P m :=
    stops_of_moments (K := K) (P := P) (Z := Z) (c := d) H
  have paid : PaidSix P (m 0) (m 1) (m 2) (m 3) :=
    interior_paid_of_moments (K := K) (P := P) (Z := Z) (d := d) H
  change ∃ s t : K, t ≠ 0 ∧ P = C t*threeInteriorProfile s r ∧
    ThreeInteriorNormalized s r m
  exact normalize_left (K := K) (P := P) (r := r) (m := m)
    (k := P.leadingCoeff) (e := e) he lead fac ord unit marks inj off stops paid

/-- Reflect the actual polynomial and the same four marks. No new
Moments record is required at the possibly vanishing reflected origin. -/
private theorem normalize_reflected_layout {P Z : K[X]} {d : Fin 5 → K}
    {r : Fin 3 → K} {e : K} (H : Moments P Z d) (inside : AllFourMarksInterior d)
    (L : ThreeChangeLayout P r e) (he : 1 ≤ e) :
    ∃ s t : K, t ≠ 0 ∧ P.comp (1-X) = C t*threeInteriorProfile s (threeInteriorMirror r) ∧
      ThreeInteriorNormalized s (threeInteriorMirror r) (threeInteriorMirror (interiorMarks d)) := by
  let p₁ : K[X] := P.comp (1-X)
  let e₁ : K := 1-e
  let r₁ : Fin 3 → K := threeInteriorMirror r
  let m₀ : Fin 4 → K := interiorMarks d
  let m₁ : Fin 4 → K := threeInteriorMirror m₀
  have eleft : e₁ ≤ 0 := sub_nonpos.mpr he
  have lead : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr H.qNonzero
  have fac₀ : P = C P.leadingCoeff*((X-C e)*indexedHull r Finset.univ) := L.factor
  have fac₁ : p₁ = C P.leadingCoeff*((X-C e₁)*indexedHull r₁ Finset.univ) :=
    reflect_factor (K := K) (P := P) (k := P.leadingCoeff) (e := e) (r := r) fac₀
  have ord : StrictMono r₁ := mirror_strictMono (K := K) (v := r) L.sorted
  have unit (i : Fin 3) : r₁ i ∈ Set.Ioo 0 1 :=
    mirror_inside (K := K) (v := r) L.unit i
  have marks₀ : ∀ j : Fin 4, m₀ j ∈ Set.Ioo 0 1 := inside
  have marks₁ (j : Fin 4) : m₁ j ∈ Set.Ioo 0 1 :=
    mirror_inside (K := K) (v := m₀) marks₀ j
  have inj₀ : Function.Injective m₀ := H.clockSimple.comp (Fin.succ_injective 4)
  have inj₁ : Function.Injective m₁ := mirror_injective (K := K) (v := m₀) inj₀
  have off (j : Fin 4) : p₁.eval (m₁ j) ≠ 0 := by
    have actual : P.eval (m₀ j.rev) ≠ 0 := (H.active j.rev.succ).2
    simpa only [p₁, m₁, threeInteriorMirror, eval_comp, eval_sub, eval_one, eval_X, sub_sub_cancel]
      using actual
  have stops₀ : ThreeInteriorStops P m₀ :=
    stops_of_moments (K := K) (P := P) (Z := Z) (c := d) H
  have stops₁ : ThreeInteriorStops p₁ m₁ :=
    ThreeInteriorStops.reflect (K := K) (P := P) (m := m₀) stops₀
  have paid : PaidSix p₁ (m₁ 0) (m₁ 1) (m₁ 2) (m₁ 3) :=
    interior_reflected_paid_of_moments (K := K) (P := P) (Z := Z) (d := d) H
  change ∃ s t : K, t ≠ 0 ∧ p₁ = C t*threeInteriorProfile s r₁ ∧
    ThreeInteriorNormalized s r₁ m₁
  exact normalize_left (K := K) (P := p₁) (r := r₁) (m := m₁)
    (k := P.leadingCoeff) (e := e₁) eleft lead fac₁ ord unit marks₁ inj₁ off stops₁ paid

/-- Native consumer of the literal classifier disjunct. The disjunction
identifies the actual marks and the actual (possibly reflected) polynomial. -/
theorem normalized_threeInterior_of_actual {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) (H : ThreeInterior q c) :
    ∃ E : OrderedExtension K, ∃ (s : E.carrier) (r : Fin 3 → E.carrier)
      (m : Fin 4 → E.carrier) (t : E.carrier), t ≠ 0 ∧ ThreeInteriorNormalized s r m ∧
      ((m = (fun j => E.embed (c j.succ)) ∧ q.map E.embed = C t*threeInteriorProfile s r) ∨
       (m = threeInteriorMirror (fun j => E.embed (c j.succ)) ∧
         (q.map E.embed).comp (1-X) = C t*threeInteriorProfile s r)) := by
  obtain ⟨marks, E, r, e, layout⟩ := H
  let p : E.carrier[X] := q.map E.embed
  let Zp : E.carrier[X] := Z.map E.embed
  let d : Fin 5 → E.carrier := fun i => E.embed (c i)
  let m : Fin 4 → E.carrier := interiorMarks d
  have mapped : Moments p Zp d :=
    moments_along_field (K := K) (L := E.carrier) (q := q) (Z := Z) (c := c) E.embed M
  have inside : AllFourMarksInterior d := map_interior_marks (c := c) E marks
  have packet : ThreeChangeLayout p r e := layout
  have stamp : m = (fun j : Fin 4 => E.embed (c j.succ)) := rfl
  rcases packet.outside with he | he
  · have branch : ∃ s t : E.carrier, t ≠ 0 ∧ p = C t*threeInteriorProfile s r ∧
        ThreeInteriorNormalized s r m :=
      normalize_unreflected_layout (K := E.carrier) (P := p) (Z := Zp)
        (d := d) (r := r) (e := e) mapped inside packet he
    obtain ⟨s, t, nonzero, eq, normalized⟩ := branch
    have trace : q.map E.embed = C t*threeInteriorProfile s r := eq
    exact ⟨E, s, r, m, t, nonzero, normalized, Or.inl ⟨stamp, trace⟩⟩
  · let r₁ : Fin 3 → E.carrier := threeInteriorMirror r
    let m₁ : Fin 4 → E.carrier := threeInteriorMirror m
    have branch : ∃ s t : E.carrier, t ≠ 0 ∧
        p.comp (1-X) = C t*threeInteriorProfile s r₁ ∧ ThreeInteriorNormalized s r₁ m₁ :=
      normalize_reflected_layout (K := E.carrier) (P := p) (Z := Zp)
        (d := d) (r := r) (e := e) mapped inside packet he
    obtain ⟨s, t, nonzero, eq, normalized⟩ := branch
    have trace : (q.map E.embed).comp (1-X) = C t*threeInteriorProfile s r₁ := eq
    have mirrorStamp : m₁ = threeInteriorMirror (fun j : Fin 4 => E.embed (c j.succ)) :=
      congrArg (fun v : Fin 4 → E.carrier => threeInteriorMirror v) stamp
    exact ⟨E, s, r₁, m₁, t, nonzero, normalized, Or.inr ⟨mirrorStamp, trace⟩⟩

end
end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
