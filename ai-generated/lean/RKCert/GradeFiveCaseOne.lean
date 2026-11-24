module

public import RKCert.GradeFiveSpace
public import RKCert.QuarticPrimitive
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

/-! # The two-independent-quadratic-directions case of minimal grade five -/
namespace RKCert.Paired
open Polynomial
open Module

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}

/-- In the single-chain minimal profile, the node and the head value determine
every stage evaluation through the indicated grade. -/
theorem chain_profile_eq_weights {A : Fin s → Fin s → K} {q r : ℕ} {d : Vec K s}
    (hshape : zeroSpace A q=chainSpan A d r)
    {i j : Fin s} (hc : nodes A i=nodes A j) (hd : d i=d j)
    (t : Tree) (ht : t.order ≤ q+1) :
    stageWeight A t i=stageWeight A t j := by
  have hp := t.order_pos
  have ho : (Tree.bush (t.order-1)).order=t.order := by rw [Tree.order_bush]; omega
  have h := normDiff_mem A t _ ho.symm ht
  rw [hshape,chainSpan_iff_polynomial] at h
  obtain ⟨P,hP,hEq⟩ := h
  have he := congrFun hEq i
  have he' := congrFun hEq j
  simp only [Pi.sub_apply,normTree_bush,diag_apply,evalNodes_apply] at he he'
  rw [hc,hd] at he
  have hnorm : normTree A t i = normTree A t j := by linear_combination he-he'
  simp only [normTree,Pi.smul_apply,smul_eq_mul] at hnorm
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr t.childDensityProduct_pos.ne') hnorm

/-- The minimal profile cannot have two independent directions d and Cd at grade three. -/
theorem no_minimal_five_independent {A : Fin s → Fin s → K} (ha : StrictLower A)
    (hsep : Separated A 5) (hR : finrank K (zeroSpace A 5) ≤ 4)
    (hrows : ∀ i j : Fin s, i < j → ∃ t : Tree, t.order ≤ 6 ∧ stageWeight A t i≠stageWeight A t j)
    (hind : signal A (qdef A) 1 ∉ Submodule.span K {qdef A}) : False := by
  classical
  cases s with
  | zero =>
    have h := nodes_not_zeroSpace hsep (by decide)
    apply h
    have he : nodes A=0 := by ext i; exact Fin.elim0 i
    rw [he]; exact (zeroSpace A 5).zero_mem
  | succ s =>
    let d := qdef A
    obtain ⟨h4,h5⟩ := minimal_five_chain_case ha hsep hR hind
    change zeroSpace A 4=chainSpan A d 2 at h4
    change zeroSpace A 5=chainSpan A d 3 at h5
    have hcoord {i j : Fin (s+1)} (hc : nodes A i = nodes A j) (hd : d i=d j) : i=j := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt|hlt
      · obtain ⟨t,ht,hn⟩ := hrows i j hlt
        exact hn (chain_profile_eq_weights h5 hc hd t (by omega))
      · obtain ⟨t,ht,hn⟩ := hrows j i hlt
        exact hn (chain_profile_eq_weights h5 hc.symm hd.symm t (by omega))
    have hc0 : nodes A 0=0 := by
      unfold nodes; exact Finset.sum_eq_zero fun j _ => ha _ _ (Nat.zero_le _)
    have hd0 : d 0=0 := origin_zeroSpace A ha 2 (qdef_mem A)
    have hquad : d*d∈zeroSpace A 4 := zeroSpace_mul (A:=A) (m:=2) (n:=2) (v:=d) (w:=d) (qdef_mem A) (qdef_mem A)
    rw [h4,chainSpan_iff_polynomial] at hquad
    obtain ⟨g,hg,hEq⟩ := hquad
    have hgd (i : Fin (s+1)) (hi : d i≠0) : g.eval (nodes A i)=d i := by
      have h := congrFun hEq i
      change d i*d i=d i*g.eval (nodes A i) at h
      exact (mul_left_cancel₀ hi h).symm
    have hgn : g≠0 := by
      intro hz
      apply qdef_ne_zero ha hsep
      ext i
      by_contra hn
      have h := hgd i hn
      simp [hz] at h
      exact hn h.symm
    have hclean (i : Fin (s+1)) (hi : d i=0) : ∀ v ∈ zeroSpace A 5, v i=0 := by
      intro v hv
      rw [h5,chainSpan_iff_polynomial] at hv
      obtain ⟨P,_,rfl⟩ := hv
      simp [hi]
    let P : Polynomial K := X*g
    have hdP : P.natDegree ≤ 3 := Polynomial.natDegree_mul_le_of_le (by simp) hg
    let Z := evalNodes A P - diag (nodes A) d
    have hCd : diag (nodes A) d∈zeroSpace A 3 := diag_zeroSpace A 2 (qdef_mem A)
    have hnon : Z≠0 := by
      intro hz
      have he : evalNodes A P = diag (nodes A) d := sub_eq_zero.mp hz
      have hor := hsep P (by omega) (he ▸ zeroSpace_mono A (by decide : 3 ≤ 5) hCd)
      exact (mul_ne_zero X_ne_zero hgn) hor
    have hZdef (i : Fin (s+1)) : Z i = nodes A i * (g.eval (nodes A i)-d i) := by
      simp [Z,P,mul_sub]
    have hex : ∃ i : Fin (s+1), nodes A i≠0 ∧ d i=0 := by
      obtain ⟨i,hi⟩ := Function.ne_iff.mp hnon
      have hi' : Z i≠0 := hi
      rw [hZdef] at hi'
      have hnd : d i=0 := by
        by_contra hdn
        rw [hgd i hdn,sub_self,mul_zero] at hi'
        contradiction
      exact ⟨i,(mul_ne_zero_iff.mp hi').1,hnd⟩
    let U : Set (Fin (s+1)) := { i | nodes A i≠0 ∧ d i=0 }
    obtain ⟨i,⟨hi,hdi⟩,hmin⟩ := wellFounded_lt.has_min U hex
    have hpre (j : Fin (s+1)) (hj : j < i) (hd : d j=0) : nodes A j=0 := by
      by_contra hh
      exact hmin j ⟨hh,hd⟩ hj
    have hZpre (j : Fin (s+1)) (hj : j < i) : Z j=0 := by
      rw [hZdef]
      by_cases hd : d j=0
      · rw [hpre j hj hd,zero_mul]
      · rw [hgd j hd,sub_self,mul_zero]
    have hprev := clean_five_receiver_has_six_predecessors ha i hi (hclean i hdi)
    have hZmat (j : Fin (s+1)) (hj : j ≤ i) : mat A Z j=0 := by
      apply causal_mat ha j Z
      intro k hk
      exact hZpre k (lt_of_lt_of_le hk hj)
    have hA : mat A Z - evalNodes A (primitive P)∈zeroSpace A 4 := by
      have hh := mat_zeroSpace_charZero A 3 hCd
      have h := (zeroSpace A 4).sub_mem (primitive_defect A P hdP) hh
      convert h using 1
      dsimp only [Z]
      rw [map_sub,sub_right_comm]
    rw [h4,chainSpan_iff_polynomial] at hA
    obtain ⟨h,hdh,hAZ⟩ := hA
    let T : Finset (Fin (s+1)) := (Finset.Iio i).erase 0
    have hT (j : Fin (s+1)) (hj : j∈T) : j < i ∧ d j≠0 := by
      obtain ⟨hneq,hji⟩ := Finset.mem_erase.mp hj
      have hjlt := Finset.mem_Iio.mp hji
      refine ⟨hjlt,?_⟩
      intro hz
      exact hneq (hcoord ((hpre j hjlt hz).trans hc0.symm) (hz.trans hd0.symm))
    have hInj : Set.InjOn (nodes A) (T : Set (Fin (s+1))) := by
      intro a ha' b hb' he
      apply hcoord he
      rw [← hgd a (hT a ha').2,← hgd b (hT b hb').2,he]
    have hcard : 5 ≤ (T.image (nodes A)).card := by
      rw [Finset.card_image_of_injOn hInj]
      change 5 ≤ ((Finset.Iio i).erase 0).card
      have hi0 : (0 : Fin (s+1)) < i := by
        change (0:ℕ) < i.val; omega
      rw [Finset.card_erase_of_mem (Finset.mem_Iio.mpr hi0),Fin.card_Iio]
      omega
    let R : Polynomial K := primitive P + g*h
    have hdR : R.natDegree ≤ 4 := Polynomial.natDegree_add_le_of_degree_le
      (primitive_natDegree_le hdP) (Polynomial.natDegree_mul_le_of_le hg hdh)
    have hroot (x : K) (hx : x∈T.image (nodes A)) : R.eval x=0 := by
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
      have hh := congrFun hAZ j
      simp only [Pi.sub_apply,evalNodes_apply,diag_apply,hZmat j (hT j hj).1.le,
        ← hgd j (hT j hj).2] at hh
      simp only [R,Polynomial.eval_add,Polynomial.eval_mul]
      linear_combination -hh
    have hR0 : R=0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' R _ hroot (by omega)
    have hprod : primitive (X*g) = g * (-h) := by
      rw [mul_neg]
      exact eq_neg_of_add_eq_zero_left hR0
    have hnv := primitive_mul_X_root_free hgn (by simpa using hdh) hprod hi
    have hev := congrFun hAZ i
    simp only [Pi.sub_apply,evalNodes_apply,diag_apply,hZmat i le_rfl,hdi,zero_mul,
      zero_sub,neg_eq_zero,P] at hev
    exact hnv hev

end RKCert.Paired
