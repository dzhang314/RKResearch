module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorStoppedBracket

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Actual opposite marks for all eight stopped erasures

Reflecting the erased suffix preserves the atomic masses and reverses only
the inequalities between actual marks. The signs are then transferred from
the exact signed masses to the actual cubic-root factors at the marks.
-/
namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.OrderedPolynomialSignStrips RKCert.ReviewedNative.FiniteGaussianNodalLift
open scoped Polynomial BigOperators

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem reflected_comp_twice (B : K[X]) : (B.comp (1-X)).comp (1-X) = B := by
  rw [comp_assoc, show (1-X : K[X]).comp (1-X) = X by
    simp only [sub_comp,one_comp,X_comp,sub_sub_cancel], comp_X]

private theorem reflected_degree (B : K[X]) : (B.comp (1-X)).natDegree = B.natDegree := by
  rw [natDegree_comp,unit_right_weight_degree,mul_one]

private theorem reflect_erased_law {P : K[X]} {v ω : Fin 4 → K} {U : Finset (Fin 4)}
    (law : ExactRule (weighted (integral 0 1) (X*(1-X)*P)) U v ω 8) :
    ExactRule (weighted (integral 0 1) (X*(1-X)*P.comp (1-X))) U
      (fun i => 1-v i) ω 8 := by
  intro B bd
  let A := X*(1-X)*P*(B.comp (1-X))
  have prev := law (B.comp (1-X)) (by rwa [reflected_degree])
  change integral 0 1 A = _ at prev
  have shp : A.comp (1-X) = X*(1-X)*P.comp (1-X)*B := by
    dsimp only [A]
    rw [mul_comp,reflected_comp_twice]
    simp only [mul_comp, sub_comp, one_comp, X_comp, sub_sub_cancel]
    ring
  change integral 0 1 (X*(1-X)*P.comp (1-X)*B) = _
  have ref := integral_reflect A (0:K)
  rw [sub_zero,shp] at ref
  exact ref.trans (by simpa only [eval_comp,eval_sub,eval_one,eval_X] using prev)

private theorem hull_four (c : Fin 4 → K) :
    indexedHull c Finset.univ = (X-C (c 0))*(X-C (c 1))*(X-C (c 2))*(X-C (c 3)) := by
  rw [indexedHull,Fin.prod_univ_four]

private theorem reflect_four_factor {P S : K[X]} {c : Fin 4 → K}
    (fact : P = S*indexedHull c Finset.univ) :
    P.comp (1-X) = S.comp (1-X)*indexedHull (fun i => 1-c i) Finset.univ := by
  rw [fact,mul_comp,hull_four c,hull_four (fun i => 1-c i)]
  simp only [mul_comp,sub_comp,X_comp,C_comp,C_sub,C_1]
  ring

/-- Literal suffix analogue of the prefix bracket. The actual 1-end value
is not assumed nonzero, and no extra field extension is selected. -/
theorem threeInterior_suffix_opposite_of_erasure {v ω : Fin 4 → K} {e t : Fin 4}
    (he : t ≠ e) (in_unit : ∀ i, v i ∈ Set.Ioo 0 1) (inj : Function.Injective v)
    {P S : K[X]} (cuts : Fin 4 → K) (off : ∀ i, cuts i ≠ v t)
    (fact : P = S*indexedHull cuts Finset.univ)
    (pos : ∀ x ∈ Set.Ioo (0:K) 1, 0 < S.eval x) (pd : P.natDegree ≤ 5)
    (law : ExactRule (weighted (integral 0 1) (X*(1-X)*P))
      (Finset.univ.erase e) v ω 8)
    (paid : integral (v t) 1 ((1-X)*P) = 0) :
    ∃ i : Fin 4, i ≠ t ∧ i ≠ e ∧ v t < v i ∧ ω i*ω t < 0 := by
  have mirror_in (x : K) (hx : x ∈ Set.Ioo (0:K) 1) : 1-x ∈ Set.Ioo (0:K) 1 :=
    ⟨sub_pos.mpr hx.2, by linarith only [hx.1]⟩
  let w (i : Fin 4) := 1-v i
  have win : ∀ i, w i ∈ Set.Ioo 0 1 := fun i => mirror_in _ (in_unit i)
  have wi : Function.Injective w := by
    intro i j eq
    change 1-v i = 1-v j at eq
    exact inj (sub_right_inj.mp eq)
  have coff (j : Fin 4) : 1-cuts j ≠ w t := fun eq => off j (sub_right_inj.mp eq)
  have pp (x : K) (hx : x ∈ Set.Ioo (0:K) 1) : 0 < (S.comp (1-X)).eval x := by
    simpa only [eval_comp,eval_sub,eval_one,eval_X] using pos (1-x) (mirror_in _ hx)
  have right : integral 0 (w t) (X*P.comp (1-X)) = 0 := by
    simpa only [w,mul_comp,sub_comp,one_comp,X_comp,sub_sub_cancel]
      using (integral_reflect ((1-X)*P) (v t)).trans paid
  obtain ⟨i, it, ie, side, sg⟩ := threeInterior_prefix_opposite_of_erasure he win wi
    (fun j => 1-cuts j) coff (reflect_four_factor fact) pp
    (by rwa [reflected_degree]) (reflect_erased_law law) right
  have phys : v t < v i := by change 1-v i < 1-v t at side; linarith only [side]
  exact ⟨i,it,ie,phys,sg⟩

/-- The erased sign at a mark, stripped of the strictly positive residual. -/
def threeInteriorErasedMarkValue (r : Fin 3 → K) (m : Fin 4 → K) (e j : Fin 4) : K :=
  (m j-m e)*(indexedHull r Finset.univ).eval (m j)

/-- Three erasures at either outer stop and the actual erasure at each
inner stop. These are the full published stopped-sign tests. -/
structure ThreeInteriorStoppedErasures (r : Fin 3 → K) (m : Fin 4 → K) : Prop where
  prefixOuter : ∀ e : Fin 4, 0 ≠ e → ∃ j : Fin 4, j ≠ 0 ∧ j ≠ e ∧ m j < m 0 ∧
    threeInteriorErasedMarkValue r m e j*threeInteriorErasedMarkValue r m e 0 < 0
  prefixInner : ∃ j : Fin 4, j ≠ 1 ∧ j ≠ 0 ∧ m j < m 1 ∧
    threeInteriorErasedMarkValue r m 0 j*threeInteriorErasedMarkValue r m 0 1 < 0
  suffixOuter : ∀ e : Fin 4, 3 ≠ e → ∃ j : Fin 4, j ≠ 3 ∧ j ≠ e ∧ m 3 < m j ∧
    threeInteriorErasedMarkValue r m e j*threeInteriorErasedMarkValue r m e 3 < 0
  suffixInner : ∃ j : Fin 4, j ≠ 2 ∧ j ≠ 3 ∧ m 2 < m j ∧
    threeInteriorErasedMarkValue r m 3 j*threeInteriorErasedMarkValue r m 3 2 < 0

private theorem real_sign_of_opposite_masses {m η : Fin 4 → K} {r : Fin 3 → K} {j t e : Fin 4}
    (inj : Function.Injective m)
    (sg : ∀ i, 0 < η i*(indexedHull r Finset.univ).eval (m i))
    (je : j ≠ e) (te : t ≠ e)
    (opp : (η j*(m j-m e))*(η t*(m t-m e)) < 0) :
    threeInteriorErasedMarkValue r m e j*threeInteriorErasedMarkValue r m e t < 0 := by
  have same (i : Fin 4) (ie : i ≠ e) :
      0 < (η i*(m i-m e))*threeInteriorErasedMarkValue r m e i := by
    have hne : m i-m e ≠ 0 := sub_ne_zero.mpr (fun h => ie (inj h))
    have sh : (η i*(m i-m e))*threeInteriorErasedMarkValue r m e i =
        (η i*(indexedHull r Finset.univ).eval (m i))*(m i-m e)^2 := by
      unfold threeInteriorErasedMarkValue
      ring
    rw [sh]
    exact mul_pos (sg i) (sq_pos_of_ne_zero hne)
  have z := mul_pos (same j je) (same t te)
  have sh : ((η j*(m j-m e))*threeInteriorErasedMarkValue r m e j)*
      ((η t*(m t-m e))*threeInteriorErasedMarkValue r m e t) =
      ((η j*(m j-m e))*(η t*(m t-m e)))*
      (threeInteriorErasedMarkValue r m e j*threeInteriorErasedMarkValue r m e t) := by ring
  rw [sh] at z
  by_contra! nonneg
  exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg opp.le nonneg)) z

theorem ThreeInteriorNormalized.stopped_erasures {s : K} {r : Fin 3 → K} {m : Fin 4 → K}
    (H : ThreeInteriorNormalized s r m) : ThreeInteriorStoppedErasures r m := by
  obtain ⟨η,law,sg⟩ := H.signed_rule
  have pos (x : K) (hx : x ∈ Set.Ioo (0:K) 1) : 0 < (threeInteriorResidual s).eval x :=
    threeInterior_residual_pos ⟨H.parameter.1,H.parameter.2.le⟩ hx
  have rn (i : Fin 3) (j : Fin 4) : r i ≠ m j := by
    intro h
    have eq : (Sum.inl i : ThreeInteriorSite) = Sum.inr j :=
      H.sites_injective (show threeInteriorSites r m (Sum.inl i) = threeInteriorSites r m (Sum.inr j) from h)
    cases eq
  let cuts (e : Fin 4) : Fin 4 → K := Fin.cons (m e) r
  have off {t e : Fin 4} (te : t ≠ e) (i : Fin 4) : cuts e i ≠ m t := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact fun h => te ((H.markDistinct h).symm)
    · exact rn _ _
  have fac (e : Fin 4) : threeInteriorErasedProfile s r (m e) =
      threeInteriorResidual s*indexedHull (cuts e) Finset.univ := by
    simp only [threeInteriorErasedProfile,threeInteriorProfile,cuts,indexedHull,Fin.prod_univ_succ,
      Fin.cons_zero,Fin.cons_succ]
    ring
  have pre {t e : Fin 4} (te : t ≠ e)
      (paid : integral 0 (m t) (X*threeInteriorErasedProfile s r (m e)) = 0) :
      ∃ j : Fin 4, j ≠ t ∧ j ≠ e ∧ m j < m t ∧
        threeInteriorErasedMarkValue r m e j*threeInteriorErasedMarkValue r m e t < 0 := by
    obtain ⟨j,jt,je,ord,opp⟩ := threeInterior_prefix_opposite_of_erasure te H.markInside
      H.markDistinct (cuts e) (off te) (fac e) pos (threeInterior_erased_degree s r _)
      (threeInterior_erased_rule law e) paid
    exact ⟨j,jt,je,ord,real_sign_of_opposite_masses H.markDistinct sg je te opp⟩
  have suf {t e : Fin 4} (te : t ≠ e)
      (paid : integral (m t) 1 ((1-X)*threeInteriorErasedProfile s r (m e)) = 0) :
      ∃ j : Fin 4, j ≠ t ∧ j ≠ e ∧ m t < m j ∧
        threeInteriorErasedMarkValue r m e j*threeInteriorErasedMarkValue r m e t < 0 := by
    obtain ⟨j,jt,je,ord,opp⟩ := threeInterior_suffix_opposite_of_erasure te H.markInside
      H.markDistinct (cuts e) (off te) (fac e) pos (threeInterior_erased_degree s r _)
      (threeInterior_erased_rule law e) paid
    exact ⟨j,jt,je,ord,real_sign_of_opposite_masses H.markDistinct sg je te opp⟩
  exact ⟨fun e te => pre te (H.stops.erase_left_outer (m e)),
    pre (by decide : (1 : Fin 4) ≠ 0) H.stops.erase_left_inner,
    fun e te => suf te (H.stops.erase_right_outer (m e)),
    suf (by decide : (2 : Fin 4) ≠ 3) H.stops.erase_right_inner⟩

end
end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
