module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorSevenRule

import Mathlib.Tactic.Ring

@[expose] public section

/-! # Exact signed atomic law and single erasures at every actual stop

This signs the four mark masses and drops any erased atom at the proper
new degree-eight budget. The final prefix/suffix bracket and finite word
reduction are separate consumers.
-/

namespace RKCert.ReviewedNative.FiniteGaussianNodalLift

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

theorem weighted_exact_of_degree_charge {ι : Type*} {J : K[X] →ₗ[K] K} {t : Finset ι}
    {v μ : ι → K} {D b : ℕ} (law : ExactRule J t v μ D) (P : K[X])
    (paid : P.natDegree+b ≤ D) :
    ExactRule (weighted J P) t v (fun i => μ i*P.eval (v i)) b := by
  intro Q qd
  rw [weighted_apply, law _ ((natDegree_mul_le_of_le (le_refl P.natDegree) qd).trans paid)]
  apply Finset.sum_congr rfl
  intro i _
  rw [eval_mul, mul_assoc]

end RKCert.ReviewedNative.FiniteGaussianNodalLift

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.PositiveRule19 RKCert.ReviewedNative.FiniteOrderedSigns
open RKCert.ReviewedNative.OrderedPolynomialSignStrips RKCert.ReviewedNative.FiniteGaussianNodalLift
open scoped Polynomial BigOperators

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def threeInteriorSignedMoment (s : K) (r : Fin 3 → K) : K[X] →ₗ[K] K :=
  weighted (integral 0 1) (X*(1-X)*threeInteriorProfile s r)

theorem threeInterior_mark_nodal_shape (m : Fin 4 → K) :
    Lagrange.nodal Finset.univ m = rawFourHull (m 0) (m 1) (m 2) (m 3) := by
  rw [Lagrange.nodal, Fin.prod_univ_four, rawFourHull]
  ring

set_option maxHeartbeats 800000 in
theorem ThreeInteriorNormalized.signed_rule {s : K} {r : Fin 3 → K} {m : Fin 4 → K}
    (H : ThreeInteriorNormalized s r m) :
    ∃ η : Fin 4 → K, ExactRule (threeInteriorSignedMoment s r) Finset.univ m η 9 ∧
      ∀ i, 0 < η i * (indexedHull r Finset.univ).eval (m i) := by
  let S : Finset (Fin 4) := Finset.univ
  let J := threeInteriorSignedMoment s r
  let η := cardinalMass J S m
  let T := indexedHull r Finset.univ
  have td : T.natDegree = 3 := by simp [T]
  have tn : T ≠ 0 := (indexedHull_monic r Finset.univ).ne_zero
  have law : ExactRule J S m η 9 := by
    refine exact_of_bounded_annihilates J S m H.markDistinct.injOn (b := 5) (by simp [S]) ?_
    intro Q qd
    have g := H.global Q qd
    change integral 0 1 (X*(1-X)*threeInteriorProfile s r*(Lagrange.nodal Finset.univ m*Q)) = 0
    rw [threeInterior_mark_nodal_shape]
    simpa only [mul_assoc] using g
  refine ⟨η, law, ?_⟩
  intro i
  let P := Lagrange.basis S m i
  have hi : i ∈ S := Finset.mem_univ i
  have pd : P.natDegree ≤ 3 := by
    have d : P.natDegree = S.card-1 := Lagrange.natDegree_basis H.markDistinct.injOn hi
    simpa [S] using d.le
  have pn : P ≠ 0 := by
    have ev : P.eval (m i) = 1 := Lagrange.eval_basis_self H.markDistinct.injOn hi
    exact fun e => one_ne_zero (ev.symm.trans (by rw [e, eval_zero]))
  have psqd : (P^2).natDegree ≤ 6 := natDegree_pow_le_of_le 2 pd
  have weighted_law : ExactRule (weighted J T) S m (fun j => η j*T.eval (m j)) 6 :=
    weighted_exact_of_degree_charge law T (by rw [td])
  change 0 < η i*T.eval (m i)
  rw [mass_eq_cardinal_square_of_degree H.markDistinct.injOn weighted_law hi psqd]
  change 0 < integral 0 1 (X*(1-X)*threeInteriorProfile s r*(T*P^2))
  have shape :
      X*(1-X)*threeInteriorProfile s r*(T*P^2) = threeInteriorDensity s*(T*P)^2 := by
    unfold threeInteriorDensity threeInteriorProfile T
    ring
  rw [shape]
  have tpd : (T*P).natDegree ≤ 6 := natDegree_mul_le_of_le td.le pd
  have sqd : ((T*P)^2).natDegree ≤ 12 := natDegree_pow_le_of_le 2 tpd
  have deg : (threeInteriorDensity s*(T*P)^2).natDegree ≤ 19 :=
    (natDegree_mul_le_of_le (threeInterior_density_degree s) sqd).trans (by decide)
  have pos (j : Fin 19) : 0 < (threeInteriorDensity s).eval (intervalPoint (0:K) 1 j) :=
    threeInterior_density_pos ⟨H.parameter.1,H.parameter.2.le⟩ (intervalPoint_mem zero_lt_one j)
  apply integral_pos_of_grid_samples zero_lt_one deg
  · intro j
    rw [eval_mul, eval_pow]
    exact mul_nonneg (pos j).le (sq_nonneg _)
  · obtain ⟨j, hj⟩ := exists_nonzero_grid_sample zero_lt_one (mul_ne_zero tn pn)
      (tpd.trans_lt (by decide : 6 < 19))
    refine ⟨j, ?_⟩
    rw [eval_mul, eval_pow]
    exact mul_pos (pos j) (sq_pos_of_ne_zero hj)

def threeInteriorErasedProfile (s : K) (r : Fin 3 → K) (e : K) : K[X] :=
  (X-C e)*threeInteriorProfile s r

theorem threeInterior_erased_rule {s : K} {r : Fin 3 → K} {m η : Fin 4 → K}
    (law : ExactRule (threeInteriorSignedMoment s r) Finset.univ m η 9)
    (e : Fin 4) :
    ExactRule (weighted (integral 0 1) (X*(1-X)*threeInteriorErasedProfile s r (m e)))
      (Finset.univ.erase e) m (fun i => η i*(m i-m e)) 8 := by
  have adj : ExactRule (weighted (threeInteriorSignedMoment s r) (X-C (m e)))
      Finset.univ m (fun i => η i*(X-C (m e)).eval (m i)) 8 :=
    weighted_exact_of_degree_charge law _ (by rw [natDegree_X_sub_C])
  intro Q qd
  have h := adj Q qd
  simp only [weighted_apply, eval_sub, eval_X, eval_C] at h
  have eq :
      X*(1-X)*threeInteriorProfile s r*((X-C (m e))*Q) =
        X*(1-X)*threeInteriorErasedProfile s r (m e)*Q := by
    unfold threeInteriorErasedProfile
    ring
  change integral 0 1 (X*(1-X)*threeInteriorProfile s r*((X-C (m e))*Q)) = _ at h
  rw [eq] at h
  rw [weighted_apply, h]
  symm
  have eras := Finset.sum_erase_add Finset.univ
    (fun i => η i*(m i-m e)*Q.eval (m i)) (Finset.mem_univ e)
  simpa only [sub_self, mul_zero, zero_mul, add_zero] using eras

theorem ThreeInteriorStops.erase_left_outer {P : K[X]} {m : Fin 4 → K}
    (H : ThreeInteriorStops P m) (e : K) :
    integral 0 (m 0) (X*((X-C e)*P)) = 0 := by
  rw [show X*((X-C e)*P) = X^2*P-C e*(X*P) by ring, map_sub,
    threeInterior_integral_C_mul, H.l1, H.l2, mul_zero, sub_zero]

theorem ThreeInteriorStops.erase_right_outer {P : K[X]} {m : Fin 4 → K}
    (H : ThreeInteriorStops P m) (e : K) :
    integral (m 3) 1 ((1-X)*((X-C e)*P)) = 0 := by
  have eq : (1-X)*((X-C e)*P) = C (1-e)*((1-X)*P)-(1-X)^2*P := by
    simp only [C_sub, C_1]
    ring
  rw [eq, map_sub, threeInterior_integral_C_mul, H.r1, H.r2, mul_zero, sub_zero]

theorem ThreeInteriorStops.erase_left_inner {P : K[X]} {m : Fin 4 → K}
    (H : ThreeInteriorStops P m) :
    integral 0 (m 1) (X*((X-C (m 0))*P)) = 0 := by
  simpa only [mul_assoc] using H.la

theorem ThreeInteriorStops.erase_right_inner {P : K[X]} {m : Fin 4 → K}
    (H : ThreeInteriorStops P m) :
    integral (m 2) 1 ((1-X)*((X-C (m 3))*P)) = 0 := by
  rw [show (1-X)*((X-C (m 3))*P) = -((1-X)*(C (m 3)-X)*P) by ring,
    map_neg, H.rh, neg_zero]

end
end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
