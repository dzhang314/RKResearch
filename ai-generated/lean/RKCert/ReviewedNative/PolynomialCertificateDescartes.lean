module

public import RKCert.ReviewedNative.PolynomialCertificateSignBudget
public import RKCert.ReviewedNative.PolynomialCertificateBox
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Order.Interval.Finset.Fin

import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Conditional root cages from exact sign budgets

Descartes is consumed through Mathlib's algebraic theorem. An ordered tuple
of actual distinct sites is supplied by the caller; no roots at other
parameter points, splitting hypotheses, or positive quadrature weights
are required. The resulting cages can overlap. -/

namespace RKCert.ReviewedNative.PolynomialCertificate

open Function Polynomial
open scoped Polynomial

noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- For roots strictly above x use the translate by x. -/
def abovePoly (p : K[X]) (x : K) : K[X] := p.taylor x

/-- For roots strictly below x negate the translated variable. -/
def belowPoly (p : K[X]) (x : K) : K[X] := (p.taylor x).comp (-X)

@[simp] theorem abovePoly_natDegree (p : K[X]) (x : K) :
    (abovePoly p x).natDegree = p.natDegree :=
  Polynomial.natDegree_taylor p x

@[simp] theorem belowPoly_natDegree (p : K[X]) (x : K) :
    (belowPoly p x).natDegree = p.natDegree := by
  rw [belowPoly, Polynomial.natDegree_comp, Polynomial.natDegree_neg,
    Polynomial.natDegree_X, mul_one, Polynomial.natDegree_taylor]

theorem abovePoly_ne_zero {p : K[X]} (hp : p ≠ 0) (x : K) :
    abovePoly p x ≠ 0 :=
  (Polynomial.taylor_eq_zero x p).not.mpr hp

theorem belowPoly_ne_zero {p : K[X]} (hp : p ≠ 0) (x : K) :
    belowPoly p x ≠ 0 := by
  unfold belowPoly
  exact Polynomial.comp_neg_X_eq_zero_iff.not.mpr
    ((Polynomial.taylor_eq_zero x p).not.mpr hp)

theorem abovePoly_coeff (p : K[X]) (x : K) (j : ℕ) :
    (abovePoly p x).coeff j = ((Polynomial.hasseDeriv j) p).eval x :=
  Polynomial.taylor_coeff x p j

theorem belowPoly_coeff (p : K[X]) (x : K) (j : ℕ) :
    (belowPoly p x).coeff j = ((Polynomial.hasseDeriv j) p).eval x * (-1 : K) ^ j := by
  unfold belowPoly
  rw [show (-X : K[X]) = C (-1 : K) * X by simp,
    Polynomial.comp_C_mul_X_coeff, Polynomial.taylor_coeff]

private theorem card_filter_le_descartes {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : K[X]} (hq : q ≠ 0) (test : ι → Prop) [DecidablePred test]
    (f : ι → K) (hinj : Injective f)
    (hroot : ∀ i, test i → 0 < f i ∧ q.IsRoot (f i)) :
    (Finset.univ.filter test).card ≤ q.signVariations := by
  let S : Finset ι := Finset.univ.filter test
  let R : Multiset K := q.roots.filter fun x => 0 < x
  have hsubset : S.image f ⊆ R.toFinset := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have ht : test i := (Finset.mem_filter.mp hi).2
    obtain ⟨positive, zero⟩ := hroot i ht
    exact Multiset.mem_toFinset.mpr (Multiset.mem_filter.mpr
      ⟨(Polynomial.mem_roots hq).mpr zero, positive⟩)
  calc
    S.card = (S.image f).card := (Finset.card_image_of_injective S hinj).symm
    _ ≤ R.toFinset.card := Finset.card_le_card hsubset
    _ ≤ R.card := Multiset.toFinset_card_le R
    _ = q.roots.countP (fun x => 0 < x) := by simp only [R, Multiset.countP_eq_card_filter]
    _ ≤ q.signVariations := Polynomial.roots_countP_pos_le_signVariations q

/-- This bound applies even to an injectively listed subset of the roots. -/
theorem card_sites_above_le_variations {n : ℕ} {p : K[X]} (hp : p ≠ 0)
    {β : Fin n → K} (hinj : Injective β) (hroot : ∀ i, p.IsRoot (β i)) (x : K) :
    (Finset.univ.filter (fun i => x < β i)).card ≤ (abovePoly p x).signVariations := by
  refine card_filter_le_descartes (abovePoly_ne_zero hp x) (fun i => x < β i)
    (fun i => β i - x) ?_ ?_
  · intro i j h
    apply hinj
    linarith only [h]
  · intro i hi
    refine ⟨sub_pos.mpr hi, ?_⟩
    change (p.taylor x).eval (β i - x) = 0
    rw [Polynomial.taylor_eval_sub]
    exact hroot i

theorem card_sites_below_le_variations {n : ℕ} {p : K[X]} (hp : p ≠ 0)
    {β : Fin n → K} (hinj : Injective β) (hroot : ∀ i, p.IsRoot (β i)) (x : K) :
    (Finset.univ.filter (fun i => β i < x)).card ≤ (belowPoly p x).signVariations := by
  refine card_filter_le_descartes (belowPoly_ne_zero hp x) (fun i => β i < x)
    (fun i => x - β i) ?_ ?_
  · intro i j h
    apply hinj
    linarith only [h]
  · intro i hi
    refine ⟨sub_pos.mpr hi, ?_⟩
    change ((p.taylor x).comp (-X)).eval (x - β i) = 0
    rw [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X, neg_sub,
      Polynomial.taylor_eval_sub]
    exact hroot i

/-- The lower endpoint needs a bound on strictly smaller roots only.
In particular a site exactly at the endpoint does not cost a sign flip. -/
theorem le_site_of_below_variations {n : ℕ} {p : K[X]} (hp : p ≠ 0)
    {β : Fin n → K} (hsorted : StrictMono β) (hroot : ∀ i, p.IsRoot (β i))
    (i : Fin n) {l : K} (hlim : (belowPoly p l).signVariations ≤ i.val) : l ≤ β i := by
  by_contra! bad
  have hh : Finset.Iic i ⊆ Finset.univ.filter (fun j => β j < l) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (hsorted.monotone (Finset.mem_Iic.mp hj)).trans_lt bad⟩
  have hcount := (Finset.card_le_card hh).trans
    ((card_sites_below_le_variations hp hsorted.injective hroot l).trans hlim)
  rw [Fin.card_Iic] at hcount
  omega

theorem site_le_of_above_variations {n : ℕ} {p : K[X]} (hp : p ≠ 0)
    {β : Fin n → K} (hsorted : StrictMono β) (hroot : ∀ i, p.IsRoot (β i))
    (i : Fin n) {u : K} (hlim : (abovePoly p u).signVariations ≤ n - (i.val + 1)) :
    β i ≤ u := by
  by_contra! bad
  have hh : Finset.Ici i ⊆ Finset.univ.filter (fun j => u < β j) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      bad.trans_le (hsorted.monotone (Finset.mem_Ici.mp hj))⟩
  have hcount := (Finset.card_le_card hh).trans
    ((card_sites_above_le_variations hp hsorted.injective hroot u).trans hlim)
  rw [Fin.card_Ici] at hcount
  have hi := i.isLt
  omega

/-- Conditional cage with exact, computable sign budgets for the two
translated coefficient intervals. The four coefficient bound functions
belong to the two endpoint tests, not to the roots themselves. -/
theorem site_mem_Icc_of_coeffVariationBudget {n d : ℕ} {p : K[X]}
    (hp : p ≠ 0) (hd : p.natDegree ≤ d) {β : Fin n → K}
    (hsorted : StrictMono β) (hroot : ∀ i, p.IsRoot (β i)) (i : Fin n)
    {l u : K} {low₁ high₁ low₂ high₂ : ℕ → K}
    (hbelow : ∀ j ≤ d, low₁ j ≤ (belowPoly p l).coeff j ∧ (belowPoly p l).coeff j ≤ high₁ j)
    (habove : ∀ j ≤ d, low₂ j ≤ (abovePoly p u).coeff j ∧ (abovePoly p u).coeff j ≤ high₂ j)
    (bl : coeffVariationBudget d low₁ high₁ ≤ i.val)
    (bu : coeffVariationBudget d low₂ high₂ ≤ n - (i.val + 1)) :
    β i ∈ Set.Icc l u := by
  refine ⟨le_site_of_below_variations hp hsorted hroot i ?_,
    site_le_of_above_variations hp hsorted hroot i ?_⟩
  · exact (signVariations_le_coeffVariationBudget (by simpa only [belowPoly_natDegree] using hd)
      hbelow).trans bl
  · exact (signVariations_le_coeffVariationBudget (by simpa only [abovePoly_natDegree] using hd)
      habove).trans bu

/-- Full box-to-cage consumer: bound each translated coefficient at the
box vertices, evaluate a finite sign budget, and enclose the selected
actual site. Coefficients need only be separately affine on the supplied
family; roots away from the actual parameter are never assumed to exist. -/
theorem site_mem_Icc_of_vertex_coeffVariationBudget {m n d : ℕ}
    (p : (Fin m → K) → K[X]) {L U x : Fin m → K}
    (hx : ∀ j, x j ∈ Set.Icc (L j) (U j))
    (hp : p x ≠ 0) (hd : (p x).natDegree ≤ d) {β : Fin n → K}
    (hsorted : StrictMono β) (hroot : ∀ i, (p x).IsRoot (β i)) (i : Fin n)
    {l u : K} {low₁ high₁ low₂ high₂ : ℕ → K}
    (affBelow : ∀ j ≤ d, SeparatelyAffine (fun y => (belowPoly (p y) l).coeff j))
    (affAbove : ∀ j ≤ d, SeparatelyAffine (fun y => (abovePoly (p y) u).coeff j))
    (vertexBelow : ∀ (e : Fin m → Bool) (j : ℕ), j ≤ d →
      (belowPoly (p (vertex L U e)) l).coeff j ∈ Set.Icc (low₁ j) (high₁ j))
    (vertexAbove : ∀ (e : Fin m → Bool) (j : ℕ), j ≤ d →
      (abovePoly (p (vertex L U e)) u).coeff j ∈ Set.Icc (low₂ j) (high₂ j))
    (bl : coeffVariationBudget d low₁ high₁ ≤ i.val)
    (bu : coeffVariationBudget d low₂ high₂ ≤ n - (i.val + 1)) :
    β i ∈ Set.Icc l u := by
  apply site_mem_Icc_of_coeffVariationBudget hp hd hsorted hroot i _ _ bl bu
  · intro j hj
    exact value_in_Icc_of_vertices (affBelow j hj) hx (fun e => vertexBelow e j hj)
  · intro j hj
    exact value_in_Icc_of_vertices (affAbove j hj) hx (fun e => vertexAbove e j hj)

end

end RKCert.ReviewedNative.PolynomialCertificate
