module

public import RKCert.ReviewedNative.NativeModularFactorLift
public import RKCert.ReviewedNative.NativeLobatto43

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The 160 complementary Lobatto factor tests modulo 181

Kernel evaluation uses only a six-step coefficient recurrence over the
finite field. The recurrence is verified against the actual product of
the selected linear factors. The residue transport first matches a factor
in an abstract field, then applies an already-mapped finite certificate. -/

namespace RKResearch.Certified.Graded.NativeLobatto

open Polynomial NativeModularRootLift
open scoped BigOperators

/-- We clear all possible denominators i+2, 0 ≤ i ≤ 5. -/
def firstPrimitiveRates : Fin 6 → ℕ := ![210,140,105,84,70,60]

theorem firstPrimitiveRates_clear (i : Fin 6) :
    firstPrimitiveRates i * (i.val+2) = 420 := by
  fin_cases i <;> decide

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Polynomial-in-coefficients representative of 420 times the first
weighted primitive (for a factor of degree at most five). -/
def clearedLobattoFirst (P : R[X]) (t : R) : R :=
  ∑ i : Fin 6, (firstPrimitiveRates i : R) * P.coeff i.val * t^(i.val+2)

theorem map_clearedLobattoFirst (q : R →+* S) (P : R[X]) (t : R) :
    q (clearedLobattoFirst P t) = clearedLobattoFirst (P.map q) (q t) := by
  simp only [clearedLobattoFirst, map_sum, map_mul, map_pow, map_natCast, coeff_map]

/-- The degree-six monic model after the literal scaling t ↦ 132t. -/
noncomputable def scaledLobattoWithOrigin : ℤ[X] := X * scaledLobatto

theorem scaledLobattoWithOrigin_monic : scaledLobattoWithOrigin.Monic :=
  monic_X.mul scaledLobatto_monic

theorem scaledLobattoWithOrigin_degree : scaledLobattoWithOrigin.natDegree = 6 := by
  rw [scaledLobattoWithOrigin, natDegree_X_mul scaledLobatto_monic.ne_zero,
    scaledLobatto_degree]

private noncomputable def subsetPolynomial (l : List (R × Bool)) : R[X] :=
  (l.map (fun p => if p.2 then X - C p.1 else 1)).prod

private def subsetCoeff : List (R × Bool) → ℕ → R
  | [], i => if i = 0 then 1 else 0
  | (_, false) :: l, i => subsetCoeff l i
  | (x, true) :: l, 0 => -(x * subsetCoeff l 0)
  | (x, true) :: l, i+1 => subsetCoeff l i - x * subsetCoeff l (i+1)

private theorem subsetCoeff_eq (l : List (R × Bool)) (i : ℕ) :
    subsetCoeff l i = (subsetPolynomial l).coeff i := by
  induction l generalizing i with
  | nil =>
      simp [subsetCoeff, subsetPolynomial, coeff_one]
  | cons p l ih =>
      obtain ⟨x,b⟩ := p
      cases b
      · simp [subsetCoeff, subsetPolynomial, ih]
      · cases i with
        | zero =>
            simp [subsetCoeff, subsetPolynomial, ih, sub_mul, coeff_sub, coeff_X_mul_zero,
              coeff_C_mul]
        | succ i =>
            simp [subsetCoeff, subsetPolynomial, ih, coeff_X_sub_C_mul]

private theorem subsetPolynomial_eq_prod {ιn : ℕ} (r : Fin ιn → R) (b : Fin ιn → Bool) :
    subsetPolynomial (List.ofFn fun i => (r i, b i)) =
      ∏ i, (if b i then X - C (r i) else 1) := by
  simp only [subsetPolynomial, List.map_ofFn, List.prod_ofFn, Function.comp_apply]

set_option maxRecDepth 4096 in
theorem prime181 : Nat.Prime 181 := by decide
local instance : Fact (Nat.Prime 181) := ⟨prime181⟩

private abbrev z181 := Int.castRingHom (ZMod 181)

/-- Zero followed by the five scaled nonzero nodes, in the original
mod-181 Lobatto order. -/
private def labels181 : Fin 6 → ZMod 181 := ![0,167,13,66,119,146]

private theorem labels181_injective : Function.Injective labels181 := by
  intro i j h
  revert h
  fin_cases i <;> fin_cases j <;> decide

private theorem scaled_eval181 (x : ZMod 181) :
    (scaledLobattoWithOrigin.map z181).eval x =
      x * (x^5 - 330*x^4 + 300*132*x^3 - 120*132^2*x^2 + 20*132^3*x - 132^4) := by
  rw [scaledLobattoWithOrigin, Polynomial.map_mul, Polynomial.map_X, eval_mul, eval_X]
  simp [scaledLobatto, ofFn_eq_sum_monomial, Fin.sum_univ_succ, scaledCoefficients]
  <;> ring
  all_goals first | exact Or.inl True.intro | trivial

private theorem labels181_root (i : Fin 6) :
    (scaledLobattoWithOrigin.map z181).IsRoot (labels181 i) := by
  change (scaledLobattoWithOrigin.map z181).eval (labels181 i)=0
  rw [scaled_eval181]
  fin_cases i <;> decide

private theorem scaledLobatto_mod181 :
    scaledLobattoWithOrigin.map z181 = ∏ i : Fin 6, (X - C (labels181 i)) := by
  apply eq_prod_of_monic_label_roots labels181 labels181_injective _
    (scaledLobattoWithOrigin_monic.map _) _ labels181_root
  rw [scaledLobattoWithOrigin_monic.natDegree_map, scaledLobattoWithOrigin_degree]
  simp

theorem scaledLobatto_mod181_separable :
    (scaledLobattoWithOrigin.map (Int.castRingHom (ZMod 181))).Separable := by
  rw [scaledLobatto_mod181]
  exact separable_prod (pairwise_coprime_X_sub_C labels181_injective)
    (fun _ => separable_X_sub_C)

private def maskMoment (pivot : Fin 5) (b : Fin 6 → Bool) : ZMod 181 :=
  let l := List.ofFn (fun i => (labels181 i, b i))
  let t := labels181 pivot.succ
  210 * subsetCoeff l 0 * t^2 + 140 * subsetCoeff l 1 * t^3 +
    105 * subsetCoeff l 2 * t^4 + 84 * subsetCoeff l 3 * t^5 +
    70 * subsetCoeff l 4 * t^6 + 60 * subsetCoeff l 5 * t^7

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 4000 in
private theorem literal_mask_nonzero (i : Fin 5) (a b c d e f : Bool) :
    (![a,b,c,d,e,f] : Fin 6 → Bool) i.succ = false →
    maskMoment i ![a,b,c,d,e,f] ≠ 0 := by
  fin_cases i <;> cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

private theorem mask_nonzero (i : Fin 5) (b : Fin 6 → Bool) (notPivot : b i.succ=false) :
    maskMoment i b ≠ 0 := by
  have eq : (![b 0,b 1,b 2,b 3,b 4,b 5] : Fin 6 → Bool) = b := by
    funext j
    fin_cases j <;> rfl
  have h : (![b 0,b 1,b 2,b 3,b 4,b 5] : Fin 6 → Bool) i.succ = false := by
    rw [eq,notPivot]
  simpa only [eq] using literal_mask_nonzero i (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) h

private theorem maskMoment_eq (i : Fin 5) (b : Fin 6 → Bool) :
    maskMoment i b =
      clearedLobattoFirst (∏ j : Fin 6, if b j then X - C (labels181 j) else 1)
        (labels181 i.succ) := by
  rw [← subsetPolynomial_eq_prod labels181 b]
  simp [maskMoment, clearedLobattoFirst, firstPrimitiveRates, subsetCoeff_eq,
    Fin.sum_univ_succ, add_assoc]

-- Keep Bool-decide conversion on generic monoid products. Elaborating the
-- original nested product directly in Polynomial (ZMod 181) forced the
-- full coefficient-ring instance into a definitional equality check.
private theorem product_of_member_bits {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [CommMonoid M] (T : Finset ι) (F : ι → M) :
    Finset.univ.prod (fun i => if decide (i ∈ T) then F i else 1) = T.prod F := by
  calc
    _ = Finset.univ.prod (fun i => if i ∈ T then F i else 1) := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases h : i ∈ T <;> simp [h]
    _ = _ := Fintype.prod_ite_mem T F

private theorem subset_nonzero181 (i : Fin 5) (T : Finset (Fin 6)) (h : i.succ ∉ T) :
    clearedLobattoFirst (T.prod (fun j => (X : (ZMod 181)[X]) - C (labels181 j)))
      (labels181 i.succ) ≠ 0 := by
  let b : Fin 6 → Bool := fun j => decide (j ∈ T)
  have b0 : b i.succ = false := decide_eq_false_iff_not.mpr h
  have shape :
      Finset.univ.prod (fun j => if b j then (X : (ZMod 181)[X]) - C (labels181 j) else 1) =
        T.prod (fun j => (X : (ZMod 181)[X]) - C (labels181 j)) :=
    product_of_member_bits T (fun j => (X : (ZMod 181)[X]) - C (labels181 j))
  have eq := maskMoment_eq i b
  rw [shape] at eq
  exact eq ▸ mask_nonzero i b b0

-- Give elaboration a syntactic boundary for a product and its mapped
-- version. The coefficient ring, the labels and the finset are opaque
-- parameters in the two generic proofs below.
private noncomputable def labelFactorProduct {F : Type*} [CommRing F]
    (r : Fin 6 → F) (T : Finset (Fin 6)) : F[X] :=
  T.prod (fun j => (X : F[X]) - C (r j))

private theorem labelFactorProduct_map {F E : Type*} [CommRing F] [CommRing E]
    (q : F →+* E) (r : Fin 6 → F) (T : Finset (Fin 6)) :
    (labelFactorProduct r T).map q = labelFactorProduct (fun j => q (r j)) T := by
  simp only [labelFactorProduct, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C]

private theorem labelFactorProduct_locate_root {F : Type*} [Field F]
    (r : Fin 6 → F) {t : F} (hr : (labelFactorProduct r Finset.univ).IsRoot t) :
    ∃ j : Fin 6, t = r j := by
  have hz := hr.eq_zero
  rw [labelFactorProduct, eval_prod] at hz
  simp only [eval_sub, eval_X, eval_C] at hz
  obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hz
  exact ⟨j, sub_eq_zero.mp hj⟩

/-- No specialization by characteristic or prime-field instance happens
while locating the target index and complement. -/
private theorem labeled_monic_complement {F : Type*} [Field F]
    (r : Fin 6 → F) (ri : Function.Injective r) (r0 : r 0 = 0)
    (P : F[X]) (pm : P.Monic) (pd : P ∣ labelFactorProduct r Finset.univ)
    (t : F) (tn : t ≠ 0)
    (root : (labelFactorProduct r Finset.univ).IsRoot t) (notRoot : ¬ P.IsRoot t) :
    ∃ (i : Fin 5) (T : Finset (Fin 6)),
      t = r i.succ ∧ i.succ ∉ T ∧ P = labelFactorProduct r T := by
  obtain ⟨j, atj⟩ := labelFactorProduct_locate_root r root
  have j0 : j ≠ 0 := by
    intro z
    exact tn (atj.trans ((congrArg r z).trans r0))
  obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr j0
  have ti : t = r i.succ := atj.trans (congrArg r hi).symm
  have dv : P ∣ ∏ j, (X - C (r j)) := pd
  obtain ⟨T, mem, eq⟩ := monic_divisor_eq_label_subproduct r ri P pm dv
  have out : i.succ ∉ T := by
    intro inside
    apply notRoot
    rw [ti]
    exact (mem _).mp inside
  exact ⟨i, T, ti, out, eq⟩

private theorem labels181_zero : labels181 (0 : Fin 6) = 0 := rfl

-- Base change is a separate small equality, not an in-line rewrite of
-- whichever polynomial happens to contain the concrete finite product.
private theorem scaledLobatto_labels_after_map {F : Type*} [CommRing F]
    (q : ZMod 181 →+* F) :
    scaledLobattoWithOrigin.map (Int.castRingHom F) =
      labelFactorProduct (fun j => q (labels181 j)) Finset.univ := by
  have compat : scaledLobattoWithOrigin.map (Int.castRingHom F) =
      (scaledLobattoWithOrigin.map z181).map q := by
    rw [Polynomial.map_map]
    exact congrArg (fun f : ℤ →+* F => scaledLobattoWithOrigin.map f) (RingHom.ext_int _ _)
  rw [compat, scaledLobatto_mod181]
  exact labelFactorProduct_map q labels181 Finset.univ

private theorem mapped_subset_nonzero181 {F : Type*} [Field F]
    (q : ZMod 181 →+* F) (i : Fin 5) (T : Finset (Fin 6)) (out : i.succ ∉ T) :
    clearedLobattoFirst (labelFactorProduct (fun j => q (labels181 j)) T)
      (q (labels181 i.succ)) ≠ 0 := by
  let B : (ZMod 181)[X] := labelFactorProduct labels181 T
  let t : ZMod 181 := labels181 i.succ
  have base : clearedLobattoFirst B t ≠ 0 := subset_nonzero181 i T out
  have mapB : B.map q = labelFactorProduct (fun j => q (labels181 j)) T :=
    labelFactorProduct_map q labels181 T
  have transport : q (clearedLobattoFirst B t) =
      clearedLobattoFirst (labelFactorProduct (fun j => q (labels181 j)) T) (q t) :=
    (map_clearedLobattoFirst q B t).trans
      (congrArg (fun V : F[X] => clearedLobattoFirst V (q t)) mapB)
  intro h
  exact base (q.injective ((transport.trans h).trans (map_zero q).symm))

/-- Every reduced monic factor avoiding the specified nonzero node has
nonzero cleared first primitive. The field is not restricted to ZMod 181.
Only the prime-field ring hom and abstract typed equalities are composed
in this theorem; no coefficient recurrence unfolds in its proof. -/
theorem clearedLobattoFirst_ne_zero_at_residue_factor
    {k : Type*} [Field k] [CharP k 181] (P : k[X]) (pm : P.Monic)
    (pd : P ∣ scaledLobattoWithOrigin.map (Int.castRingHom k)) (t : k) (tn : t ≠ 0)
    (troot : (scaledLobattoWithOrigin.map (Int.castRingHom k)).IsRoot t)
    (notRoot : ¬ P.IsRoot t) :
    clearedLobattoFirst P t ≠ 0 := by
  let q : ZMod 181 →+* k := ZMod.castHom (dvd_refl (181 : ℕ)) k
  let r : Fin 6 → k := fun j => q (labels181 j)
  have ri : Function.Injective r := q.injective.comp labels181_injective
  have r0 : r 0 = 0 := (congrArg q labels181_zero).trans (map_zero q)
  have fac : scaledLobattoWithOrigin.map (Int.castRingHom k) =
      labelFactorProduct r Finset.univ := scaledLobatto_labels_after_map q
  have pd' : P ∣ labelFactorProduct r Finset.univ := fac ▸ pd
  have rt' : (labelFactorProduct r Finset.univ).IsRoot t := fac ▸ troot
  obtain ⟨i, T, ti, out, eq⟩ := labeled_monic_complement r ri r0 P pm pd' t tn rt' notRoot
  rw [eq, ti]
  exact mapped_subset_nonzero181 q i T out

end RKResearch.Certified.Graded.NativeLobatto
