module
public import RKCert.ReviewedNative.ERK8CharElevenHighExclusion
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! The literal five-off center prefix and paid primitive absence bound. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven.FiveOff

open RKResearch Polynomial Module OneOff ERKTaggedHorizon ERK8PaidField LobattoEight RKCert.Endpoint
open RKResearch.Certified.Graded.ERK8CharEleven
open scoped Matrix Classical BigOperators

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}


/-- The clean center and its actual strict prefix. Later clean clocks
may include the two roots of q, so no clean-tag count is hidden here. -/
structure CenterPrefix (A : Matrix (Fin 10) (Fin 10) K) (h : Fin 10) : Prop where
  origin_clock : nodes A 0=0
  origin_clean : g A 0=0
  center_clock : nodes A h=6
  center_clean : g A h=0
  hpos : (0:Fin 10)<h
  hlast : h<Fin.last 9
  clean_before : ∀ j, j<h → g A j=0 → j=0
  at_least_three : 3≤(offPrefixClocks A h).card

theorem five_clean_of_literal (ha : ∀ i j, i≤j → A i j=0)
    (ho : HasOrder 8 A b) (five : (offKnots A).card=5) :
    (cleanKnots A).card=5 := by
  rcases order8_count_one_four_five_seven ha ho with h|⟨h,_⟩|⟨_,h⟩|⟨h,_⟩ <;> omega

theorem center_prefix_of_literal
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (five : (offKnots A).card=5) (cleanFive : (cleanKnots A).card=5) :
    ∃ (theta : K) (h : Fin 10), ExceptionalHead A theta ∧ CenterPrefix A h := by
  obtain ⟨theta,h,H,hg,hc,pre,hc3⟩ :=
    order8_five_seven_exceptional_prefix ha ho p (Or.inl five)
  have zero : nodes A (0:Fin 10)=0 := by
    change (∑ j, A 0 j*1)=0
    exact Finset.sum_eq_zero fun j _ => by rw [ha 0 j (Fin.zero_le _),zero_mul]
  have g0 : g A 0=0 := origin_zeroSpace (s:=9) ha 2 (mDef_mem A 1)
  have six0 : (6:K)≠0 := (ho.natCast_isUnit (n:=6) (by decide) (by decide)).ne_zero
  have five0 : (5:K)≠0 := (ho.natCast_isUnit (n:=5) (by decide) (by decide)).ne_zero
  have six1 : (6:K)≠1 := fun e => five0 (by linear_combination e)
  have i0 : h≠0 := fun e => six0 (hc.symm.trans ((congrArg (nodes A) e).trans zero))
  have i9 : h≠Fin.last 9 := fun e => six1 (hc.symm.trans ((congrArg (nodes A) e).trans H.terminal_clock))
  refine ⟨theta,h,H,zero,g0,hc,hg,lt_of_le_of_ne (Fin.zero_le _) i0.symm,
    lt_of_le_of_ne (Fin.le_last _) i9,?_,hc3⟩
  intro j hj gj
  have inj := (order8_tag_injective_of_full_count (A:=A) (by omega)).1
  exact inj j 0 gj g0 ((pre j hj gj).trans zero.symm)

theorem high_center_clean_before {h j : Fin 10} (S : CenterPrefix A h)
    (jh : j<h) (gj : g A j=0) : j=0 := S.clean_before j jh gj

theorem high_off_before_center {h j : Fin 10} (S : CenterPrefix A h)
    (jpos : 0<j) (jh : j<h) : g A j≠0 :=
  fun gj => (ne_of_gt jpos) (high_center_clean_before S jh gj)

theorem high_center_off_prefix_card
    (five : (offKnots A).card=5) (cleanFive : (cleanKnots A).card=5)
    {h : Fin 10} (S : CenterPrefix A h) :
    (offPrefixClocks A h).card + 1 = h.val := by
  let D : Finset (Fin 10) := (Finset.Iio h).erase 0
  have e : ((Finset.univ : Finset (Fin 10)).filter (fun j => j<h ∧ g A j≠0))=D := by
    ext j
    simp only [D,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,Finset.mem_Iio]
    constructor
    · rintro ⟨lt,gj⟩
      exact ⟨fun h => gj (h.symm ▸ S.origin_clean),lt⟩
    · rintro ⟨nz,lt⟩
      exact ⟨lt,fun gj => nz (high_center_clean_before S lt gj)⟩
  have inj := (order8_tag_injective_of_full_count (A:=A) (by omega)).2
  have map : (D.image (nodes A)).card=D.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb he
    rw [←e] at ha hb
    exact inj a b (Finset.mem_filter.mp ha).2.2 (Finset.mem_filter.mp hb).2.2 he
  have pren : D.card+1=(Finset.Iio h).card :=
    Finset.card_erase_add_one (Finset.mem_Iio.mpr S.hpos)
  rw [Fin.card_Iio] at pren
  rw [offPrefixClocks,e,map]
  exact pren
theorem high_precenter_xq_profile
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b)
    {theta : K} (H : ExceptionalHead A theta) {h : Fin 10} (S : CenterPrefix A h) :
    ∃ R : K[X], R.natDegree≤2 ∧
      ∀ j, j<h → g A j≠0 →
        (primitive (X*(exceptionalQuadratic : K[X]))).eval (nodes A j)=
          (exceptionalQuadratic : K[X]).eval (nodes A j)*R.eval (nodes A j) := by
  let q : K[X] := exceptionalQuadratic
  let B : Fin 10→K := theta⁻¹ • diag (nodes A) (g A)
  have bmem : B∈zeroSpace A 3 :=
    (zeroSpace A 3).smul_mem _ (diag_zeroSpace A 2 (mDef_mem A 1))
  have Amem := mat_zeroSpace ho 3 (by decide) bmem
  have dq : (X*q).natDegree≤3 :=
    natDegree_mul_le_of_le (show (X:K[X]).natDegree≤1 by simp) exceptionalQuadratic_degree
  have dif := primitive_defect_paid ho (X*q) dq (by decide)
  have mem := (zeroSpace A 4).sub_mem Amem dif
  rw [H.fourthBand] at mem
  obtain ⟨R,Rd,he⟩ := band_iff.mp mem
  refine ⟨C theta*R,(natDegree_C_mul_le _ _).trans Rd,?_⟩
  intro j jh gj
  have equiv : mat A (evalNodes A (X*q)) j=mat A B j := by
    apply causal_action_eq ha
    intro i ij
    have ih := ij.trans jh
    simp only [evalNodes_apply,eval_mul,eval_X,B,Pi.smul_apply,smul_eq_mul,diag_apply]
    by_cases gi : g A i=0
    · have i0 := high_center_clean_before S ih gi
      simp [i0,S.origin_clock]
    · have e : theta⁻¹*g A i=q.eval (nodes A i) := by
        rw [←H.fit i gi,←mul_assoc,inv_mul_cancel₀ H.scale_ne,one_mul]
      rw [mul_left_comm (theta⁻¹),e]
  have eq := congrFun he j
  simp only [Pi.sub_apply,diag_apply,evalNodes_apply,equiv] at eq
  rw [←H.fit j gj] at eq
  simp only [eval_mul,eval_C]
  linear_combination eq

/-- The first center occurs at physical row 4 or 5. This excludes later
centers directly by a nonzero degree-four polynomial, not by a scan. -/
theorem high_center_four_or_five
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (five : (offKnots A).card=5) (cleanFive : (cleanKnots A).card=5)
    {theta : K} (H : ExceptionalHead A theta) {h : Fin 10} (S : CenterPrefix A h) :
    h=4 ∨ h=5 := by
  obtain ⟨R,dR,Rfit⟩ := high_precenter_xq_profile ha ho H S
  let W := primitive (X*(exceptionalQuadratic : K[X]))-exceptionalQuadratic*R
  have wn : W≠0 := q_times_linear_nf_nonzero ho p R
  have pd : (primitive (X*(exceptionalQuadratic : K[X]))).natDegree≤4 :=
    primitive_natDegree_le (natDegree_mul_le_of_le
      (show (X:K[X]).natDegree≤1 by simp) exceptionalQuadratic_degree)
  have qd : ((exceptionalQuadratic : K[X])*R).natDegree≤4 :=
    natDegree_mul_le_of_le exceptionalQuadratic_degree dR
  have wd : W.natDegree≤4 := natDegree_sub_le_of_le pd qd
  have wr (x : K) (hx : x∈offPrefixClocks A h) : W.eval x=0 := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨lt,gi⟩ := (Finset.mem_filter.mp hi).2
    simp [W,Rfit i lt gi]
  have hcard : (offPrefixClocks A h).card≤4 := by
    by_contra! hb
    exact wn (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' W _ wr (by omega))
  have actual := high_center_off_prefix_card five cleanFive S
  have lo := S.at_least_three
  have hh : h.val=4 ∨ h.val=5 := by omega
  rcases hh with h4|h5
  · exact Or.inl (Fin.ext h4)
  · exact Or.inr (Fin.ext h5)

end RKResearch.Certified.Graded.ERK8CharEleven.FiveOff

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.FiveOff.center_prefix_of_literal
#print axioms RKResearch.Certified.Graded.ERK8CharEleven.FiveOff.high_center_four_or_five
