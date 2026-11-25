module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorActualErasures
public import RKCert.ReviewedNative.WeakFiveThreeInteriorOrderWords
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.FinRange

import Mathlib.Tactic.Choose
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The nine published orders are earned from the actual packet

Ranks are those of the actual seven split sites. The real predecessor and
eraser inequalities are transported to these ranks; the values of the
four nonzero linear factors are used only through their signs.
-/
namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.OrderedPolynomialSignStrips
open RKCert.ReviewedNative.OrderedRootGapSaturation RKCert.ReviewedNative.WeakFive16
open scoped Polynomial

universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem actual_ranks (v : ThreeInteriorSite → K) (inj : Function.Injective v) :
    ∃ (p : List (Fin 7)) (β : Fin 7 → K), p.Perm (List.finRange 7) ∧
      StrictMono β ∧ ∀ j, β (threeInteriorRank p j) = v j := by
  classical
  let f : Fin 7 → K := v ∘ threeInteriorToken.symm
  have fi : Function.Injective f := inj.comp threeInteriorToken.symm.injective
  let S := Finset.univ.image f
  have cs : S.card = 7 := by simp [S,Finset.card_image_of_injective _ fi]
  let β := S.orderEmbOfFin cs
  have each (i : Fin 7) : ∃ j : Fin 7, β j = f i := by
    have mem : f i ∈ S := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    have ranges : Set.range β = (S : Set K) := S.range_orderEmbOfFin cs
    have actual : f i ∈ Set.range β := by rw [ranges]; exact mem
    exact actual
  choose rank loc using each
  have ranki : Function.Injective rank := by
    intro a b eq
    apply fi
    rw [← loc a,← loc b,eq]
  have onto : Function.Surjective rank := Finite.surjective_of_injective ranki
  let p := List.ofFn rank
  have perm : p.Perm (List.finRange 7) := by
    refine (List.perm_ext_iff_of_nodup (List.nodup_ofFn_ofInjective ranki)
      (List.nodup_finRange 7)).mpr ?_
    intro i
    refine ⟨fun _ => by simp,fun _ => ?_⟩
    exact List.mem_ofFn.mpr (onto i)
  refine ⟨p,β,perm,β.strictMono,?_⟩
  intro j
  have code : threeInteriorRank p j = rank (threeInteriorToken j) := by
    simp only [threeInteriorRank,p,List.getD,List.getElem?_ofFn,dif_pos (threeInteriorToken j).isLt,
      Option.getD_some]
  rw [code,loc]
  simp only [f,Function.comp_apply,Equiv.symm_apply_apply]

private theorem rank_factor_real {a b : Fin 7} {x y : K} (rel : a < b ↔ x < y) :
    x-y = (threeInteriorRankFactorSign a b : K)*|x-y| := by
  by_cases h : a < b
  · rw [threeInteriorRankFactorSign,if_pos h,Int.cast_neg,Int.cast_one,
      abs_of_neg (sub_neg.mpr (rel.mp h)),neg_one_mul,neg_neg]
  · have nonneg : 0 ≤ x-y := sub_nonneg.mpr (le_of_not_gt (fun gt => h (rel.mpr gt)))
    rw [threeInteriorRankFactorSign,if_neg h,Int.cast_one,abs_of_nonneg nonneg,one_mul]

private theorem sign_opposition_on_ranks {s : K} {r : Fin 3 → K} {m : Fin 4 → K}
    (H : ThreeInteriorNormalized s r m) {p : List (Fin 7)}
    (rel : ∀ a b : ThreeInteriorSite, threeInteriorRank p a < threeInteriorRank p b ↔
      threeInteriorSites r m a < threeInteriorSites r m b)
    {e j t : Fin 4} (je : j ≠ e) (te : t ≠ e)
    (op : threeInteriorErasedMarkValue r m e j*threeInteriorErasedMarkValue r m e t < 0) :
    threeInteriorRankErasedSign p e j*threeInteriorRankErasedSign p e t < 0 := by
  let mag (i : Fin 4) := |m i - m e| * (|m i - r 0| * |m i - r 1| * |m i - r 2|)
  have diff (i : Fin 4) (k : Fin 3) :
      m i-r k =
        (threeInteriorRankFactorSign (threeInteriorRankMark p i) (threeInteriorRankRoot p k) : K)*
          |m i-r k| :=
    rank_factor_real (rel (.inr i) (.inl k))
  have shape (i : Fin 4) :
      threeInteriorErasedMarkValue r m e i = (threeInteriorRankErasedSign p e i : K)*mag i := by
    have em : m i-m e =
        (threeInteriorRankFactorSign (threeInteriorRankMark p i) (threeInteriorRankMark p e) : K)*
          |m i-m e| :=
      rank_factor_real (rel (.inr i) (.inr e))
    simp only [threeInteriorErasedMarkValue,threeInterior_hull_three,eval_mul,eval_sub,eval_X,eval_C]
    conv_lhs => rw [em,diff i 0,diff i 1,diff i 2]
    simp only [threeInteriorRankErasedSign,Int.cast_mul,mag]
    ring
  have rn (i : Fin 4) (k : Fin 3) : 0 < |m i-r k| := by
    apply abs_pos.mpr
    intro z
    have bad : (Sum.inr i : ThreeInteriorSite) = Sum.inl k :=
      H.sites_injective (show threeInteriorSites r m (.inr i) = threeInteriorSites r m (.inl k)
        from sub_eq_zero.mp z)
    cases bad
  have mp (i : Fin 4) (ie : i ≠ e) : 0 < mag i :=
    mul_pos (abs_pos.mpr (sub_ne_zero.mpr (fun eq => ie (H.markDistinct eq))))
      (mul_pos (mul_pos (rn i 0) (rn i 1)) (rn i 2))
  let Z : ℤ := threeInteriorRankErasedSign p e j*threeInteriorRankErasedSign p e t
  have h := op
  rw [shape j,shape t,show ((threeInteriorRankErasedSign p e j : K)*mag j)*
      ((threeInteriorRankErasedSign p e t : K)*mag t) = (Z:K)*(mag j*mag t) by
    simp only [Z,Int.cast_mul]
    ring] at h
  have neg : (Z:K) < 0 := by
    by_contra! nn
    exact (not_lt_of_ge (mul_nonneg nn (mul_pos (mp j je) (mp t te)).le)) h
  have fin : Z < 0 := by exact_mod_cast neg
  exact fin

/-- The former chronology callback is now supplied by the actual
normalized moments, not by a remembered or numerically chosen order. -/
theorem threeInterior_orderReceipt : ThreeInteriorOrderReceipt (K := K) := by
  intro s r m H
  obtain ⟨p,β,perm,sorted,locate⟩ := actual_ranks (threeInteriorSites r m) H.sites_injective
  have rel (a b : ThreeInteriorSite) :
      threeInteriorRank p a < threeInteriorRank p b ↔ threeInteriorSites r m a < threeInteriorSites r m b := by
    rw [← locate a,← locate b]
    exact sorted.lt_iff_lt.symm
  have mRel (a b : Fin 4) : threeInteriorRankMark p a < threeInteriorRankMark p b ↔ m a < m b :=
    rel (.inr a) (.inr b)
  let W := H.local_windows
  let E := H.stopped_erasures
  have fwd {t e : Fin 4} (te : t ≠ e)
      (hh : ∃ j : Fin 4, j ≠ t ∧ j ≠ e ∧ m j < m t ∧
        threeInteriorErasedMarkValue r m e j*threeInteriorErasedMarkValue r m e t < 0) :
      threeInteriorOrdinalOpposite p true t e := by
    obtain ⟨j,jt,je,side,opp⟩ := hh
    exact ⟨j,jt,je,Or.inl ⟨rfl,(mRel j t).mpr side⟩,sign_opposition_on_ranks H rel je te opp⟩
  have rev {t e : Fin 4} (te : t ≠ e)
      (hh : ∃ j : Fin 4, j ≠ t ∧ j ≠ e ∧ m t < m j ∧
        threeInteriorErasedMarkValue r m e j*threeInteriorErasedMarkValue r m e t < 0) :
      threeInteriorOrdinalOpposite p false t e := by
    obtain ⟨j,jt,je,side,opp⟩ := hh
    exact ⟨j,jt,je,Or.inr ⟨rfl,(mRel t j).mpr side⟩,sign_opposition_on_ranks H rel je te opp⟩
  have adm : ThreeInteriorOrdinalOK p := by
    refine ⟨(rel (.inl 0) (.inl 1)).mpr (H.rootOrder (by decide)),
      (rel (.inl 1) (.inl 2)).mpr (H.rootOrder (by decide)),
      (rel (.inl 1) (.inr 0)).mpr W.leftPair,(rel (.inr 3) (.inl 1)).mpr W.rightPair,?_,?_,
      fwd (by decide) (E.prefixOuter 1 (by decide)),fwd (by decide) (E.prefixOuter 2 (by decide)),
      fwd (by decide) (E.prefixOuter 3 (by decide)),fwd (by decide) E.prefixInner,
      rev (by decide) (E.suffixOuter 0 (by decide)),rev (by decide) (E.suffixOuter 1 (by decide)),
      rev (by decide) (E.suffixOuter 2 (by decide)),rev (by decide) E.suffixInner⟩
    · simpa only [threeInteriorRankRoot,threeInteriorRankMark,rel,threeInteriorSites,
        Sum.elim_inl,Sum.elim_inr] using W.leftInner
    · simpa only [threeInteriorRankRoot,threeInteriorRankMark,rel,threeInteriorSites,
        Sum.elim_inl,Sum.elim_inr] using W.rightInner
  obtain ⟨w,matchWord⟩ := threeInterior_finite_order perm adm
  have literal : w.sites r m = β := by
    funext i
    have hit := locate (w.labels i)
    rw [matchWord i] at hit
    exact hit.symm
  refine ⟨w,?_⟩
  rw [literal]
  exact sorted

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
