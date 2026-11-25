module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorNormalized
public import RKCert.ReviewedNative.FiniteGaussianNodalLift
public import RKCert.ReviewedNative.FiniteOrderedSignWindows
public import Mathlib.Data.Fintype.BigOperators

import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The actual positive degree-twelve seven-node law

The six global paid words are sufficient for degree 12, not degree 13.
No order enumeration, determinant tables, or new positivity assumption
enters this construction.
-/
namespace RKCert.ReviewedNative.FiniteGaussianNodalLift

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

/-- Bounded nodal orthogonality, without rounding the quotient allowance
up to the full Gaussian range. -/
theorem exact_of_bounded_annihilates {ι : Type*} [DecidableEq ι]
    (J : K[X] →ₗ[K] K) (t : Finset ι) (v : ι → K) (nodes : Set.InjOn v t)
    {D b : ℕ} (cost : D ≤ t.card+b)
    (annihilate : ∀ Q : K[X], Q.natDegree ≤ b → J (Lagrange.nodal t v*Q) = 0) :
    ExactRule J t v (cardinalMass J t v) D := by
  intro P pd
  let M : K[X] := Lagrange.nodal t v
  let Q := P /ₘ M
  let L := P %ₘ M
  have monic : M.Monic := Lagrange.nodal_monic (s := t) (v := v)
  have md : M.natDegree = t.card := Lagrange.natDegree_nodal
  have qd : Q.natDegree ≤ b := by
    change (P /ₘ M).natDegree ≤ b
    rw [natDegree_divByMonic P monic, md]
    omega
  have ld : L.degree < (t.card : WithBot ℕ) := by
    simpa only [M,L,Lagrange.degree_nodal] using degree_modByMonic_lt P monic
  have decomp : L + M*Q = P := modByMonic_add_div P M
  have ev (i : ι) (hi : i ∈ t) : L.eval (v i) = P.eval (v i) := by
    have h := congrArg (Polynomial.eval (v i)) decomp
    have hm : M.eval (v i) = 0 := Lagrange.eval_nodal_at_node hi
    simpa only [eval_add, eval_mul, hm, zero_mul, add_zero] using h
  have hJ : J P = J L := by
    have h := congrArg (fun S : K[X] => J S) decomp
    change J (L + Lagrange.nodal t v*Q) = J P at h
    rw [map_add, annihilate Q qd, add_zero] at h
    exact h.symm
  rw [hJ, Lagrange.eq_interpolate nodes ld, Lagrange.interpolate_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Polynomial.smul_eq_C_mul, map_smul, smul_eq_mul, ev i hi]
  exact mul_comm _ _

/-- Cardinal squares only cost twice the interpolation degree. -/
theorem mass_eq_cardinal_square_of_degree {ι : Type*} [DecidableEq ι]
    {J : K[X] →ₗ[K] K} {t : Finset ι} {v : ι → K} {μ : ι → K} {D : ℕ}
    (nodes : Set.InjOn v t) (law : ExactRule J t v μ D)
    {i : ι} (hi : i ∈ t) (paid : (Lagrange.basis t v i ^ 2).natDegree ≤ D) :
    μ i = J (Lagrange.basis t v i ^ 2) := by
  let P := Lagrange.basis t v i
  change μ i = J (P^2)
  rw [law _ paid]
  symm
  calc
    (∑ j ∈ t, μ j*(P^2).eval (v j)) = μ i*(P^2).eval (v i) := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        have hz : P.eval (v j) = 0 := Lagrange.eval_basis_of_ne hji.symm hj
        simp [eval_pow, hz]
      · intro hm
        exact (hm hi).elim
    _ = μ i := by
      have ho : P.eval (v i) = 1 := Lagrange.eval_basis_self nodes hi
      simp [eval_pow, ho]

end RKCert.ReviewedNative.FiniteGaussianNodalLift

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.PositiveRule19 RKCert.ReviewedNative.FiniteOrderedSigns
open RKCert.ReviewedNative.OrderedPolynomialSignStrips RKCert.ReviewedNative.FiniteGaussianNodalLift
open scoped Polynomial BigOperators

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

abbrev ThreeInteriorSite := Fin 3 ⊕ Fin 4

def threeInteriorSites (r : Fin 3 → K) (m : Fin 4 → K) : ThreeInteriorSite → K := Sum.elim r m

theorem ThreeInteriorNormalized.sites_inside {s : K} {r : Fin 3 → K} {m : Fin 4 → K}
    (H : ThreeInteriorNormalized s r m) :
    ∀ j : ThreeInteriorSite, threeInteriorSites r m j ∈ Set.Ioo 0 1 := by
  intro j
  cases j with
  | inl i => exact H.rootInside i
  | inr i => exact H.markInside i

theorem ThreeInteriorNormalized.sites_injective {s : K} {r : Fin 3 → K} {m : Fin 4 → K}
    (H : ThreeInteriorNormalized s r m) : Function.Injective (threeInteriorSites r m) := by
  have rz (j : Fin 3) : (threeInteriorProfile s r).eval (r j) = 0 := by
    have z : (indexedHull r Finset.univ).eval (r j) = 0 :=
      Lagrange.eval_nodal_at_node (Finset.mem_univ j)
    rw [threeInteriorProfile, eval_mul, z, mul_zero]
  have dis (i : Fin 3) (j : Fin 4) (h : r i = m j) : False :=
    H.markOffRoot j (h ▸ rz i)
  intro a b e
  cases a with
  | inl i =>
    cases b with
    | inl j => exact congrArg Sum.inl (H.rootOrder.injective e)
    | inr j => exact (dis i j e).elim
  | inr i =>
    cases b with
    | inl j => exact (dis j i e.symm).elim
    | inr j => exact congrArg Sum.inr (H.markDistinct e)

noncomputable section

def threeInteriorDensity (s : K) : K[X] := X*(1-X)*threeInteriorResidual s

def threeInteriorMoment (s : K) : K[X] →ₗ[K] K := weighted (integral 0 1) (threeInteriorDensity s)

theorem threeInterior_density_degree (s : K) : (threeInteriorDensity s).natDegree ≤ 3 := by
  have w : (1-X : K[X]).natDegree ≤ 1 :=
    natDegree_sub_le_of_le
      ((natDegree_one : (1 : K[X]).natDegree = 0).trans_le (Nat.zero_le 1))
      natDegree_X.le
  have r : (threeInteriorResidual s).natDegree ≤ 1 := by
    unfold threeInteriorResidual
    have linear : (C (1-s)*X).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans natDegree_X.le
    exact natDegree_add_le_of_le ((natDegree_C s).trans_le (Nat.zero_le 1)) linear
  exact natDegree_mul_le_of_le (natDegree_mul_le_of_le natDegree_X.le w) r

theorem threeInterior_density_pos {s x : K} (hs : s ∈ Set.Icc 0 1)
    (hx : x ∈ Set.Ioo 0 1) : 0 < (threeInteriorDensity s).eval x := by
  simp only [threeInteriorDensity, threeInteriorResidual, eval_add, eval_mul, eval_C,
    eval_sub, eval_one, eval_X]
  apply mul_pos (mul_pos hx.1 (sub_pos.mpr hx.2))
  rcases eq_or_lt_of_le hs.1 with e | p
  · rw [← e, zero_add, sub_zero, one_mul]
    exact hx.1
  · exact add_pos_of_pos_of_nonneg p (mul_nonneg (sub_nonneg.mpr hs.2) hx.1.le)

theorem threeInterior_nodal_shape (r : Fin 3 → K) (m : Fin 4 → K) :
    Lagrange.nodal Finset.univ (threeInteriorSites r m) =
      indexedHull r Finset.univ*rawFourHull (m 0) (m 1) (m 2) (m 3) := by
  rw [Lagrange.nodal, Fintype.prod_sum_type]
  change indexedHull r Finset.univ * (∏ j : Fin 4, (X-C (m j))) = _
  rw [Fin.prod_univ_four, rawFourHull]
  ring

set_option maxHeartbeats 800000 in
theorem ThreeInteriorNormalized.seven_rule {s : K} {r : Fin 3 → K} {m : Fin 4 → K}
    (H : ThreeInteriorNormalized s r m) :
    ∃ μ : ThreeInteriorSite → K, (∀ i, 0 < μ i) ∧
      ExactRule (threeInteriorMoment s) Finset.univ (threeInteriorSites r m) μ 12 := by
  let t : Finset ThreeInteriorSite := Finset.univ
  let v := threeInteriorSites r m
  let J := threeInteriorMoment s
  let μ := cardinalMass J t v
  have card : t.card = 7 := by simp [t, ThreeInteriorSite, Fintype.card_sum]
  have inj : Set.InjOn v t := H.sites_injective.injOn
  have law : ExactRule J t v μ 12 := by
    apply exact_of_bounded_annihilates J t v inj (b := 5) (by rw [card])
    intro Q qd
    have paid := H.global Q qd
    change integral 0 1 (threeInteriorDensity s*(Lagrange.nodal t v*Q)) = 0
    rw [show Lagrange.nodal t v = indexedHull r Finset.univ *
      rawFourHull (m 0) (m 1) (m 2) (m 3) from threeInterior_nodal_shape r m]
    have shape : threeInteriorDensity s*(indexedHull r Finset.univ *
        rawFourHull (m 0) (m 1) (m 2) (m 3) * Q) =
        X*(1-X)*(threeInteriorProfile s r*rawFourHull (m 0) (m 1) (m 2) (m 3))*Q := by
      unfold threeInteriorDensity threeInteriorProfile
      ring
    rw [shape]
    exact paid
  refine ⟨μ, ?_, law⟩
  intro i
  let P := Lagrange.basis t v i
  have hi : i ∈ t := Finset.mem_univ i
  have pd : P.natDegree ≤ 6 := by
    change (Lagrange.basis t v i).natDegree ≤ 6
    rw [Lagrange.natDegree_basis inj hi, card]
  have nz : P ≠ 0 := by
    have ev : P.eval (v i) = 1 := Lagrange.eval_basis_self inj hi
    exact fun e => one_ne_zero (ev.symm.trans (by rw [e, eval_zero]))
  have sqd : (P^2).natDegree ≤ 12 := natDegree_pow_le_of_le 2 pd
  rw [mass_eq_cardinal_square_of_degree inj law hi sqd]
  change 0 < integral 0 1 (threeInteriorDensity s*P^2)
  have deg : (threeInteriorDensity s*P^2).natDegree ≤ 19 :=
    (natDegree_mul_le_of_le (threeInterior_density_degree s) sqd).trans (by decide)
  have live (j : Fin 19) :
      0 < (threeInteriorDensity s).eval (intervalPoint (0:K) 1 j) :=
    threeInterior_density_pos ⟨H.parameter.1,H.parameter.2.le⟩
      (intervalPoint_mem zero_lt_one j)
  apply integral_pos_of_grid_samples zero_lt_one deg
  · intro j
    rw [eval_mul, eval_pow]
    exact mul_nonneg (live j).le (sq_nonneg _)
  · obtain ⟨j, hj⟩ := exists_nonzero_grid_sample (K := K) zero_lt_one nz
      (pd.trans_lt (by decide : 6 < 19))
    refine ⟨j, ?_⟩
    rw [eval_mul, eval_pow]
    exact mul_pos (live j) (sq_pos_of_ne_zero hj)

end
end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
