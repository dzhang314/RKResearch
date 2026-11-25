module

public import RKCert.ReviewedNative.WeakFiveSoleInnerCornerOrthogonality
public import Mathlib.Order.Interval.Finset.Fin

import Mathlib.Order.WellFounded
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Uniform decrease of the six paid Gaussian nodes

A degree-five nodal separator proves the exact monotonicity in either or
both affine density parameters. It needs neither a mixed-parameter rule
nor a root derivative, real closure, or division by a quadratic form.
The strict square on the checked unit grid costs degree at most fifteen. -/
namespace RKCert.ReviewedNative.WeakFiveSoleInnerUniform

open Polynomial
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteGaussianNodalLift
open RKCert.ReviewedNative.FiniteGaussianGridPositivity
open scoped BigOperators Classical

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The six actual distinct unit nodes of a monic orthogonal product; the
order is literal, so comparison preserves each individual node index. -/
structure SixNodes (s r : K) where
  sUnit : s ∈ Set.Icc (0 : K) 1
  rUnit : r ∈ Set.Icc (0 : K) 1
  site : Fin 6 → K
  increasing : StrictMono site
  inside : ∀ i, site i ∈ Set.Ioo (0 : K) 1
  paid : SixOrthogonal s r (Lagrange.nodal Finset.univ site)

namespace SixNodes

variable {s r : K}

/-- Supplying the six ordered roots of the original monic product is
enough. No separate nodal factorization hypothesis is needed. -/
theorem eq_nodal_of_monic_roots {P : K[X]} {v : Fin 6 → K}
    (mp : P.Monic) (dp : P.natDegree=6) (strict : StrictMono v)
    (zeros : ∀ i, P.IsRoot (v i)) :
    P = Lagrange.nodal Finset.univ v := by
  let Q := Lagrange.nodal Finset.univ v
  have mq : Q.Monic := Lagrange.nodal_monic
  have dq : Q.natDegree=6 := by simp [Q]
  by_contra ne
  let D := P-Q
  have dn : D ≠ 0 := sub_ne_zero.mpr ne
  have de : P.degree=Q.degree := by
    rw [degree_eq_natDegree mp.ne_zero,degree_eq_natDegree mq.ne_zero,dp,dq]
  have lc : P.leadingCoeff=Q.leadingCoeff :=
    (show P.leadingCoeff=1 from mp).trans (show Q.leadingCoeff=1 from mq).symm
  have dl : D.degree < P.degree := degree_sub_lt_left de mp.ne_zero lc
  rw [degree_eq_natDegree mp.ne_zero,dp] at dl
  have dt : D.natDegree < 6 := (natDegree_lt_iff_degree_lt dn).mpr dl
  have dz (i : Fin 6) : D.eval (v i)=0 := by
    change (P-Q).eval (v i)=0
    rw [eval_sub,show P.eval (v i)=0 from zeros i,
      show Q.eval (v i)=0 from Lagrange.eval_nodal_at_node (Finset.mem_univ _),sub_zero]
  apply dn
  exact eq_zero_of_natDegree_lt_card_of_eval_eq_zero D strict.injective dz (by simpa using dt)

/-- The producer accepts the actual monic product and its true roots
rather than assuming a pre-existing interpolation rule. -/
def ofMonic {P : K[X]} (hs : s ∈ Set.Icc (0 : K) 1) (hr : r ∈ Set.Icc (0 : K) 1)
    (mp : P.Monic) (dp : P.natDegree=6) (orth : SixOrthogonal s r P)
    (v : Fin 6 → K) (strict : StrictMono v) (inside : ∀ i, v i ∈ Set.Ioo (0 : K) 1)
    (zeros : ∀ i, P.IsRoot (v i)) : SixNodes s r where
  sUnit := hs
  rUnit := hr
  site := v
  increasing := strict
  inside := inside
  paid := by
    rw [←eq_nodal_of_monic_roots mp dp strict zeros]
    exact orth

def mass (N : SixNodes s r) : Fin 6 → K :=
  cardinalMass (weighted (integral 0 1) (density s r)) Finset.univ N.site

theorem exact_rule (N : SixNodes s r) :
    ExactRule (weighted (integral 0 1) (density s r)) Finset.univ N.site N.mass 11 := by
  have h := gaussian_exact_of_annihilates
    (weighted (integral 0 1) (density s r)) Finset.univ N.site N.increasing.injective.injOn
    (by
      intro H degH
      rw [weighted_apply,←mul_assoc]
      exact N.paid _ (by simpa using degH))
  simpa [mass] using h

theorem mass_pos (N : SixNodes s r) (i : Fin 6) : 0 < N.mass i := by
  have wn : density s r ≠ 0 := by
    intro z
    have h := density_eval_pos N.sUnit N.rUnit
      (show (1/2 : K) ∈ Set.Ioo (0 : K) 1 from ⟨by norm_num,by norm_num⟩)
    rw [z,eval_zero] at h
    exact lt_irrefl _ h
  have cost : (density s r).natDegree + 2*((Finset.univ : Finset (Fin 6)).card-1) < 19 := by
    simp only [Finset.card_univ,Fintype.card_fin]
    have hd := density_degree s r
    omega
  exact gaussian_mass_pos (zero_lt_one : (0 : K) < 1) (density s r) wn
    (fun j => (density_eval_pos N.sUnit N.rUnit (intervalPoint_mem zero_lt_one j)).le)
    (t := (Finset.univ : Finset (Fin 6))) (v := N.site) (μ := N.mass)
    N.increasing.injective.injOn (by simpa using N.exact_rule) cost (Finset.mem_univ i)

private theorem nodal_root_iff_range (v : Fin 6 → K) (x : K) :
    (Lagrange.nodal Finset.univ v).IsRoot x ↔ x ∈ Set.range v := by
  change (Lagrange.nodal Finset.univ v).eval x=0 ↔ _
  rw [Lagrange.eval_nodal,Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨j,_,hj⟩
    exact ⟨j,(sub_eq_zero.mp hj).symm⟩
  · rintro ⟨j,rfl⟩
    exact ⟨j,Finset.mem_univ _,sub_self _⟩

theorem parameter_unique (N M : SixNodes s r) : N.site=M.site := by
  have poly : Lagrange.nodal Finset.univ N.site = Lagrange.nodal Finset.univ M.site :=
    monic_unique N.sUnit N.rUnit Lagrange.nodal_monic Lagrange.nodal_monic
      (by simp) (by simp) N.paid M.paid
  apply (N.increasing.range_inj_of_wellFoundedLT M.increasing).mp
  ext x
  rw [←nodal_root_iff_range N.site x,←nodal_root_iff_range M.site x,poly]

end SixNodes

private def affineAt (a x : K) := a+(1-a)*x

private theorem affine_at_pos {a x : K} (ha : a ∈ Set.Icc (0 : K) 1) (hx : 0 < x) :
    0 < affineAt a x := by
  unfold affineAt
  by_cases az : a=0
  · simpa only [az,sub_zero,one_mul,zero_add] using hx
  · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne ha.1 (fun e => az e.symm))
      (mul_nonneg (sub_nonneg.mpr ha.2) hx.le)

private theorem affine_eval (a x : K) : (affineWeight a).eval x = affineAt a x := by
  simp [affineWeight,affineAt]

private def atFactor (s r t : K) := affineAt s t * affineAt r t

private theorem atFactor_pos {s r t : K} (hs : s ∈ Set.Icc (0 : K) 1)
    (hr : r ∈ Set.Icc (0 : K) 1) (ht : 0 < t) : 0 < atFactor s r t :=
  mul_pos (affine_at_pos hs ht) (affine_at_pos hr ht)

private def changeTail (s₀ r₀ s₁ r₁ t : K) : K[X] :=
  C ((s₁-s₀)*affineAt r₀ t)*affineWeight r₁ +
  C ((r₁-r₀)*affineAt s₁ t)*affineWeight s₀

private theorem affine_degree (a : K) : (affineWeight a).natDegree ≤ 1 := by
  unfold affineWeight
  apply natDegree_add_le_of_degree_le
  · simp
  · exact (natDegree_C_mul_le _ _).trans natDegree_X.le

private theorem tail_degree (s₀ r₀ s₁ r₁ t : K) :
    (changeTail s₀ r₀ s₁ r₁ t).natDegree ≤ 1 := by
  unfold changeTail
  apply natDegree_add_le_of_degree_le
  · exact (natDegree_C_mul_le _ _).trans (affine_degree r₁)
  · exact (natDegree_C_mul_le _ _).trans (affine_degree s₀)

private theorem tail_pos {s₀ r₀ s₁ r₁ t x : K}
    (s₀unit : s₀ ∈ Set.Icc (0 : K) 1) (r₀unit : r₀ ∈ Set.Icc (0 : K) 1)
    (s₁unit : s₁ ∈ Set.Icc (0 : K) 1) (r₁unit : r₁ ∈ Set.Icc (0 : K) 1)
    (hs : s₀≤s₁) (hr : r₀≤r₁) (move : s₀ < s₁ ∨ r₀ < r₁) (ht : 0 < t) (hx : 0 < x) :
    0 < (changeTail s₀ r₀ s₁ r₁ t).eval x := by
  simp only [changeTail,eval_add,eval_mul,eval_C,affine_eval]
  have a := affine_at_pos r₀unit ht
  have b := affine_at_pos r₁unit hx
  have c := affine_at_pos s₁unit ht
  have d := affine_at_pos s₀unit hx
  rcases move with h | h
  · exact add_pos_of_pos_of_nonneg (mul_pos (mul_pos (sub_pos.mpr h) a) b)
      (mul_nonneg (mul_nonneg (sub_nonneg.mpr hr) c.le) d.le)
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (mul_nonneg (sub_nonneg.mpr hs) a.le) b.le)
      (mul_pos (mul_pos (sub_pos.mpr h) c) d)

/-- Superpose the two affine differences before choosing a separating
polynomial. This uses the exact two-coordinate order, not a mixed pack. -/
private theorem density_difference (s₀ r₀ s₁ r₁ t : K) :
    C (atFactor s₁ r₁ t)*density s₀ r₀ - C (atFactor s₀ r₀ t)*density s₁ r₁ =
      (unitWeight K * changeTail s₀ r₀ s₁ r₁ t)*(X-C t) := by
  simp only [atFactor,density,changeTail,affineWeight,affineAt,map_add,map_mul,map_sub,map_one]
  ring

private def localized (s r t : K) (F : K[X]) : K :=
  weighted (integral 0 1) (density s r) ((X-C t)*F^2)

private theorem cross_strict {s₀ r₀ s₁ r₁ t : K}
    (A : SixNodes s₀ r₀) (B : SixNodes s₁ r₁) (hs : s₀≤s₁) (hr : r₀≤r₁)
    (move : s₀ < s₁ ∨ r₀ < r₁) (ht : 0 < t) {F : K[X]} (fn : F≠0) (fd : F.natDegree≤5) :
    atFactor s₀ r₀ t * localized s₁ r₁ t F <
      atFactor s₁ r₁ t * localized s₀ r₀ t F := by
  let G : K[X] := X-C t
  let W := unitWeight K * changeTail s₀ r₀ s₁ r₁ t
  have e : C (atFactor s₁ r₁ t)*(density s₀ r₀*(G*F^2)) -
      C (atFactor s₀ r₀ t)*(density s₁ r₁*(G*F^2)) = W*(G*F)^2 := by
    calc
      _ = (C (atFactor s₁ r₁ t)*density s₀ r₀-C (atFactor s₀ r₀ t)*density s₁ r₁)*(G*F^2) := by ring
      _ = _ := by rw [density_difference]; change (W*G)*(G*F^2)=W*(G*F)^2; ring
  have h := congrArg (fun p : K[X] => integral (0 : K) 1 p) e
  change integral 0 1 (_ - _) = integral 0 1 (W*(G*F)^2) at h
  simp only [map_sub,←Polynomial.smul_eq_C_mul,map_smul,smul_eq_mul] at h
  have w_pos (x : K) (hx : x ∈ Set.Ioo (0 : K) 1) : 0 < W.eval x := by
    simp only [W,eval_mul]
    exact mul_pos (unitWeight_eval_pos hx.1 hx.2)
      (tail_pos A.sUnit A.rUnit B.sUnit B.rUnit hs hr move ht hx.1)
  have wn : W≠0 := by
    intro z
    have hh := w_pos ((1 : K)/2) ⟨by norm_num,by norm_num⟩
    rw [z,eval_zero] at hh
    exact lt_irrefl _ hh
  have gd : G.natDegree ≤ 1 := (natDegree_X_sub_C t).le
  have gfn : G*F≠0 := mul_ne_zero (monic_X_sub_C t).ne_zero fn
  have gfd : (G*F).natDegree≤6 := natDegree_mul_le_of_le gd fd
  have wd : W.natDegree≤3 := natDegree_mul_le_of_le unitWeight_degree (tail_degree _ _ _ _ _)
  have pd : (W*(G*F)^2).natDegree < 19 :=
    (natDegree_mul_le_of_le wd (natDegree_pow_le_of_le 2 gfd)).trans_lt (by decide)
  have pos : 0 < integral 0 1 (W*(G*F)^2) := by
    apply integral_pos_of_grid_nonneg zero_lt_one _ (mul_ne_zero wn (pow_ne_zero 2 gfn)) pd
    intro i
    simp only [eval_mul,eval_pow]
    exact mul_nonneg (w_pos _ (intervalPoint_mem zero_lt_one i)).le (sq_nonneg _)
  rw [←h] at pos
  exact sub_pos.mp pos

private theorem localized_rule {s r : K} (N : SixNodes s r) (t : K) {F : K[X]}
    (fd : F.natDegree≤5) :
    localized s r t F = ∑ j : Fin 6, N.mass j*((N.site j-t)*(F.eval (N.site j))^2) := by
  have qd : ((X-C t)*F^2).natDegree≤11 :=
    natDegree_mul_le_of_le (natDegree_X_sub_C t).le (natDegree_pow_le_of_le 2 fd)
  unfold localized
  rw [N.exact_rule _ qd]
  simp only [eval_mul,eval_pow,eval_sub,eval_X,eval_C]

/-- Increasing either compact-coordinate parameter while not decreasing
the other strictly decreases every ordered Gaussian node. -/
theorem strictly_decreasing_nodes {s₀ r₀ s₁ r₁ : K}
    (A : SixNodes s₀ r₀) (B : SixNodes s₁ r₁) (hs : s₀≤s₁) (hr : r₀≤r₁)
    (move : s₀ < s₁ ∨ r₀ < r₁) (i : Fin 6) : B.site i < A.site i := by
  by_contra hn
  let t := A.site i
  let L : K[X] := Lagrange.nodal (Finset.Ioi i) A.site
  let R : K[X] := Lagrange.nodal (Finset.Iio i) B.site
  let F := L*R
  have fn : F≠0 := mul_ne_zero Lagrange.nodal_ne_zero Lagrange.nodal_ne_zero
  have fd : F.natDegree≤5 := by
    refine (natDegree_mul_le (p := L) (q := R)).trans ?_
    change (Lagrange.nodal (Finset.Ioi i) A.site).natDegree +
      (Lagrange.nodal (Finset.Iio i) B.site).natDegree ≤ 5
    rw [Lagrange.natDegree_nodal,Lagrange.natDegree_nodal,Fin.card_Ioi,Fin.card_Iio]
    have ii := i.isLt
    omega
  have aNonpos : localized s₀ r₀ t F ≤ 0 := by
    rw [localized_rule A t fd]
    apply Finset.sum_nonpos
    intro j _
    by_cases hj : i < j
    · have z : L.eval (A.site j)=0 := Lagrange.eval_nodal_at_node (Finset.mem_Ioi.mpr hj)
      simp [F,eval_mul,z]
    · have scales : A.site j≤t := A.increasing.monotone (le_of_not_gt hj)
      exact mul_nonpos_of_nonneg_of_nonpos (A.mass_pos j).le
        (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr scales) (sq_nonneg _))
  have bNonneg : 0 ≤ localized s₁ r₁ t F := by
    rw [localized_rule B t fd]
    apply Finset.sum_nonneg
    intro j _
    by_cases hj : j < i
    · have z : R.eval (B.site j)=0 := Lagrange.eval_nodal_at_node (Finset.mem_Iio.mpr hj)
      simp [F,eval_mul,z]
    · have scales : t≤B.site j := (le_of_not_gt hn).trans (B.increasing.monotone (le_of_not_gt hj))
      exact mul_nonneg (B.mass_pos j).le
        (mul_nonneg (sub_nonneg.mpr scales) (sq_nonneg _))
  have t0 : 0 < t := (A.inside i).1
  have aPos := atFactor_pos A.sUnit A.rUnit t0
  have bPos := atFactor_pos B.sUnit B.rUnit t0
  have hStrict := cross_strict A B hs hr move t0 fn fd
  exact (not_lt_of_ge ((mul_nonpos_of_nonneg_of_nonpos bPos.le aNonpos).trans
    (mul_nonneg aPos.le bNonneg))) hStrict

/-- Monotonicity on the full closed compact square, including equality
of either or both parameters. -/
theorem decreasing_nodes {s₀ r₀ s₁ r₁ : K}
    (A : SixNodes s₀ r₀) (B : SixNodes s₁ r₁)
    (hs : s₀≤s₁) (hr : r₀≤r₁) (i : Fin 6) : B.site i ≤ A.site i := by
  by_cases h : s₀ < s₁ ∨ r₀ < r₁
  · exact (strictly_decreasing_nodes A B hs hr h i).le
  · have e₁ : s₀=s₁ := le_antisymm hs (le_of_not_gt (fun lt => h (Or.inl lt)))
    have e₂ : r₀=r₁ := le_antisymm hr (le_of_not_gt (fun lt => h (Or.inr lt)))
    subst s₁
    subst r₁
    exact le_of_eq (congrFun (B.parameter_unique A) i)

end
end RKCert.ReviewedNative.WeakFiveSoleInnerUniform
