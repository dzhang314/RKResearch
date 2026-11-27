module
public import RKCert.ReviewedNative.ERK8CharElevenFiveEarlyPrefix
public import RKCert.ReviewedNative.ERK8CharElevenFourHead
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! The preceding-row interpolation adapter with only earlier off-tag injectivity. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven.FourOff

open RKResearch Polynomial Module OneOff ERKTaggedHorizon ERK8PaidField LobattoEight RKCert.Endpoint
open FourOffPhysical
open FiveOff (CenterPrefix)
open scoped Matrix Classical BigOperators

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

def EarlyOffDistinct (A : Matrix (Fin 10) (Fin 10) K) : Prop :=
  ∀ i j : Fin 10, i < 6 → j < 6 → g A i ≠ 0 → g A j ≠ 0 → nodes A i=nodes A j → i=j

theorem same_tag_early {dup i j : Fin 10} (R : RepeatAtEight A b dup)
    (hi : i < 8) (hj : j < 8) (s : SameTag A i j) : i=j := by
  by_contra ne
  rcases lt_or_gt_of_ne ne with lt|lt
  · exact (ne_of_lt hj) (R.unique lt s).2
  · exact (ne_of_lt hi) (R.unique lt s.symm).2

theorem early_off_distinct_of_placement {P : K[X]} {dup k : Fin 10}
    (M : Placement A b P dup k) : EarlyOffDistinct A := by
  intro i j hi hj gi gj e
  exact same_tag_early M.repeatAtEight (hi.trans (by decide)) (hj.trans (by decide))
    ⟨e,iff_of_false gi gj⟩

theorem earlyRows_off (H : CenterPrefix A 5) {n : ℕ} (n4 : n≤4) {j : Fin 10}
    (hj : j∈earlyRows n) : g A j≠0 := by
  obtain ⟨pos,ub⟩ := mem_earlyRows.mp hj
  apply FiveOff.high_off_before_center H
  · exact pos
  · change j.val<5
    omega

theorem early_row_lt_six {n : ℕ} (n4 : n≤4) {j : Fin 10} (hj : j∈earlyRows n) : j < 6 := by
  have t := (mem_earlyRows.mp hj).2
  change j.val < 6
  omega

theorem earlyNodes_inj (distinct : EarlyOffDistinct A)
    (H : CenterPrefix A 5) {n : ℕ} (n4 : n≤4) :
    Set.InjOn (nodes A) (earlyRows n : Set (Fin 10)) := by
  intro i hi j hj e
  exact distinct i j (early_row_lt_six n4 hi) (early_row_lt_six n4 hj)
    (earlyRows_off H n4 hi) (earlyRows_off H n4 hj) e

theorem earlyNodes_card (distinct : EarlyOffDistinct A)
    (H : CenterPrefix A 5) {n : ℕ} (n4 : n≤4) : (earlyNodes A n).card=n := by
  rw [earlyNodes,Finset.card_image_iff.mpr (earlyNodes_inj distinct H n4),earlyRows_card n4]
theorem earlyTop_g_profile (distinct : EarlyOffDistinct A)
    (H : CenterPrefix A 5) {n : ℕ} (n4 : n≤4) (P : K[X]) (deg : P.natDegree<n) :
    earlyTop A n (diag (g A) (evalNodes A P))=P.coeff (n-1) := by
  have inj := earlyNodes_inj distinct H n4
  have count := earlyNodes_card distinct H n4
  have concl := coeff_last_barycentric (earlyNodes A n) P (count.symm ▸ deg)
  rw [count] at concl
  rw [concl]
  change (∑ j∈earlyRows n, (((diag (g A)) (evalNodes A P)) j/g A j)/
    earlyCofactor A n (nodes A j)) =
      ∑ x∈(earlyRows n).image (nodes A), P.eval x/earlyCofactor A n x
  rw [Finset.sum_image inj]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [diag_apply,evalNodes_apply]
  rw [mul_comm (g A j),mul_div_cancel_right₀ _ (earlyRows_off H n4 hj)]

theorem earlyTop_band_zero (distinct : EarlyOffDistinct A)
    (H : CenterPrefix A 5) {n k : ℕ} (n4 : n≤4) (h : k<n-1) {w : Fin 10→K} (wb : w∈band A k) :
    earlyTop A n w=0 := by
  obtain ⟨P,Pd,e⟩ := band_iff.mp wb
  rw [e,earlyTop_g_profile distinct H n4 P (by omega)]
  exact coeff_eq_zero_of_natDegree_lt (Pd.trans_lt h)

theorem earlyTop_pure_theta (distinct : EarlyOffDistinct A)
    (H : CenterPrefix A 5) {theta : K} (T : ExceptionalHead A theta) {n : ℕ} (n4 : n≤4)
    (P : K[X]) : earlyTop A n (theta • evalNodes A P)=earlyBary A n P := by
  unfold earlyTop earlyBary earlyNodes
  rw [Finset.sum_image (earlyNodes_inj distinct H n4)]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Pi.smul_apply,smul_eq_mul,evalNodes_apply]
  rw [←T.fit j (earlyRows_off H n4 hj),mul_div_mul_left _ _ T.scale_ne]

/-- Two leading-coefficient equations for the original physical first
three or four off rows. The common gain is earned, and is not assumed
to be nonzero. -/
theorem early_paid_newton_two
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b)
    (distinct : EarlyOffDistinct A)
    (b3 : zeroSpace A 3=band A 1) {theta : K} (T : ExceptionalHead A theta) (H : CenterPrefix A 5)
    {m : ℕ} (m034 : m=3∨m=4) :
    ∃ gain : K, ∀ r : ℕ, 1≤r → r≤2 →
      ((r+1:ℕ):K)*gain*earlyBary A (m-1) (X^r)=earlyBary A m (X^(r+1)) := by
  have m3 : 3≤m := by omega
  have m4 : m≤4 := by omega
  have Mp : m-1≤4 := by omega
  have Mb : m-2≤4 := by omega
  have bm : zeroSpace A m=band A (m-2) := by
    rcases m034 with rfl|rfl
    · exact b3
    · exact T.fourthBand
  let S := earlyNodes A (m-1)
  let Base := nodalHull (earlyNodes A (m-2))
  let gain := earlyTop A m (mat A (diag (g A) (evalNodes A Base)))
  have Sc : S.card=m-1 := earlyNodes_card distinct H Mp
  have Bd : Base.natDegree=m-2 :=
    (natDegree_nodalHull _).trans (earlyNodes_card distinct H Mb)
  have Bc : Base.coeff (m-2)=1 := by
    have t : Base.coeff Base.natDegree=1 := (monic_nodalHull _).coeff_natDegree
    rwa [Bd] at t
  refine ⟨gain,?_⟩
  intro r r1 r2
  let P : K[X] := X^r
  let q : K[X] := exceptionalQuadratic
  let values (x : K) := P.eval x/q.eval x
  let U := Lagrange.interpolate S id values
  have Ud : U.natDegree≤m-2 := by
    by_cases u : U=0
    · simp [u]
    have d := (natDegree_lt_iff_degree_lt u).mpr
      (Lagrange.degree_interpolate_lt values (Set.injOn_id _) (s:=S))
    change U.natDegree < S.card at d
    omega
  let alpha := U.coeff (m-2)
  have Ua (x : K) (hx : x∈S) : U.eval x=values x :=
    Lagrange.eval_interpolate_at_node values (Set.injOn_id _) hx
  have alphaEq : alpha=earlyBary A (m-1) P := by
    have lc := coeff_last_barycentric S U (by omega)
    rw [Sc,show m-1-1=m-2 by omega] at lc
    change alpha=(∑ x∈S,U.eval x/earlyCofactor A (m-1) x) at lc
    rw [lc]
    unfold earlyBary
    apply Finset.sum_congr rfl
    intro x hx
    rw [Ua x hx]
  let V := U-C alpha*Base
  have CBd : (C alpha*Base).natDegree≤m-2 := (natDegree_C_mul_le _ _).trans Bd.le
  have Vd : V.natDegree≤m-3 := by
    have w : V.natDegree≤m-2 := by simpa [V] using natDegree_sub_le_of_le Ud CBd
    have c : V.coeff (m-2)=0 := by simp [V,coeff_C_mul,Bc,alpha]
    apply natDegree_le_of_last_coeff_zero (k:=m-3)
    · exact w.trans (by omega)
    · convert c using 2; omega
  have input :
      diag (g A) (evalNodes A U)=
        diag (g A) (evalNodes A V)+alpha • diag (g A) (evalNodes A Base) := by
    ext j
    simp only [V,diag_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,evalNodes_apply,eval_sub,eval_mul,eval_C]
    ring
  have eq (j : Fin 10) (hj : j∈earlyRows m) :
      mat A (theta • evalNodes A P) j=mat A (diag (g A) (evalNodes A U)) j := by
    apply causal_action_eq ha
    intro i ij
    simp only [Pi.smul_apply,smul_eq_mul,evalNodes_apply,diag_apply]
    by_cases i0 : i=0
    · subst i
      have z := H.origin_clean
      simp [z,P,H.origin_clock,zero_pow (Nat.ne_of_gt r1)]
    have pos : 0 < i.val := by
      by_contra! nz
      exact i0 (Fin.ext (by omega))
    have iP : i∈earlyRows (m-1) := by
      have jm := (mem_earlyRows.mp hj).2
      change i.val < j.val at ij
      exact mem_earlyRows.mpr ⟨pos,by omega⟩
    have hx : nodes A i∈S := Finset.mem_image.mpr ⟨i,iP,rfl⟩
    have gi := earlyRows_off H Mp iP
    have qi := exceptional_quadratic_ne_off T gi
    rw [Ua _ hx,←T.fit i gi]
    change theta*P.eval (nodes A i)=
      theta*q.eval (nodes A i)*(P.eval (nodes A i)/q.eval (nodes A i))
    rw [mul_assoc,mul_div_cancel₀ _ qi]
  have Vmem : diag (g A) (evalNodes A V)∈zeroSpace A (m-1) := by
    have z := band_le A (m-3) (band_iff.mpr ⟨V,Vd,rfl⟩)
    rw [show 2+(m-3)=m-1 by omega] at z
    exact z
  have AV : mat A (diag (g A) (evalNodes A V))∈band A (m-2) := by
    have z : mat A (diag (g A) (evalNodes A V))∈zeroSpace A (m-1+1) :=
      mat_zeroSpace ho (m-1) (by omega) Vmem
    rwa [show m-1+1=m by omega,bm] at z
  have lhs : earlyTop A m (mat A (theta • evalNodes A P))=alpha*gain := by
    rw [earlyTop_congr A eq,input,map_add,map_smul,earlyTop_add,earlyTop_smul,
      earlyTop_band_zero distinct H m4 (by omega) AV,zero_add]
  have Pd : P.natDegree≤2 := (natDegree_X_pow_le _).trans r2
  have ds := primitive_defect_paid ho P Pd (by decide : 2+1≤8)
  have dsm := (zeroSpace A 3).smul_mem theta ds
  rw [smul_sub,←map_smul,b3] at dsm
  have rhs := earlyTop_band_zero distinct H m4 (k:=1) (by omega) dsm
  rw [earlyTop_sub,lhs,earlyTop_pure_theta distinct H T m4,sub_eq_zero] at rhs
  have I : primitive P=C (1/((r+1:ℕ):K))*X^(r+1) := by
    have pmon : P=monomial r (1:K) := by simp [P,←C_mul_X_pow_eq_monomial]
    rw [pmon,primitive_monomial,←C_mul_X_pow_eq_monomial]
  rw [I,earlyBary_Cmul,alphaEq] at rhs
  have nz : (((r+1:ℕ):K))≠0 := (ho.natCast_isUnit (by omega) (by omega)).ne_zero
  have one := mul_div_cancel₀ (1:K) nz
  linear_combination (((r+1:ℕ):K))*rhs+earlyBary A m (X^(r+1))*one

end RKResearch.Certified.Graded.ERK8CharEleven.FourOff

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.FourOff.early_paid_newton_two
