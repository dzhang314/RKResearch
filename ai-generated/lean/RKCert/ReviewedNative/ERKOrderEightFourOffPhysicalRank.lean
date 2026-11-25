module

public import RKCert.ReviewedNative.ERKOrderEightTaggedCensus
public import RKCert.ReviewedNative.UnitBetaSquareMass

import Lean.Elab.Tactic.Omega
import Mathlib.LinearAlgebra.Lagrange

@[expose] public section

/-! # Actual tagged rank and clean masses for the ERK8 four-off branch

This derives the physical rank package from the measured census and actual
order. It does not assign chronological positions to noninitial senders.
-/
namespace RKResearch.Certified.Graded.FourOffPhysical

open RKResearch Module Polynomial Reverse OneOff ERKTaggedHorizon RKCert.Endpoint
open scoped Matrix Classical

section Tags

variable {K : Type*} [Field K] {s : ℕ}

/-- Two physical stages agree as tags only if both clock and defect branch agree. -/
def SameTag (A : Matrix (Fin s) (Fin s) K) (i j : Fin s) : Prop :=
  nodes A i = nodes A j ∧ (g A i = 0 ↔ g A j = 0)

theorem SameTag.symm {A : Matrix (Fin s) (Fin s) K} {i j : Fin s}
    (h : SameTag A i j) : SameTag A j i := ⟨h.1.symm, h.2.symm⟩

theorem onOffSpace_apply_eq {A : Matrix (Fin s) (Fin s) K} {v : Fin s → K}
    (hv : v ∈ onOffSpace A) {i j : Fin s} (same : SameTag A i j) :
    v i = v j := by
  obtain ⟨z,rfl⟩ := hv
  by_cases hi : g A i=0
  · have hj := same.2.mp hi
    rw [onOffEval_on A z hi, onOffEval_on A z hj]
    exact congrArg z.1 (Subtype.ext same.1)
  · have hj : g A j≠0 := fun hj => hi (same.2.mpr hj)
    rw [onOffEval_off A z hi, onOffEval_off A z hj]
    exact congrArg z.2 (Subtype.ext same.1)

-- These three generic statements are the published tagged interpolation
-- slices of OrderNineMultiStates, now in the measured thin tag namespace.
theorem onOffEval_injective (A : Matrix (Fin s) (Fin s) K) : Function.Injective (onOffEval A) := by
  intro x y h
  apply Prod.ext
  · funext a
    obtain ⟨i,hi,hc⟩ := mem_cleanKnots.mp a.property
    have he := congrFun h i
    rw [onOffEval_on A x hi,onOffEval_on A y hi] at he
    have ha : (⟨nodes A i,mem_cleanKnots.mpr ⟨i,hi,rfl⟩⟩ : cleanKnots A)=a := Subtype.ext hc
    rwa [ha] at he
  · funext a
    obtain ⟨i,hi,hc⟩ := mem_offKnots.mp a.property
    have he := congrFun h i
    rw [onOffEval_off A x hi,onOffEval_off A y hi] at he
    have ha : (⟨nodes A i,mem_offKnots.mpr ⟨i,hi,rfl⟩⟩ : offKnots A)=a :=
      Subtype.ext hc
    rwa [ha] at he

theorem onOffSpace_rank (A : Matrix (Fin s) (Fin s) K) :
    finrank K (onOffSpace A) = (cleanKnots A).card + (offKnots A).card := by
  rw [onOffSpace,LinearMap.finrank_range_of_inj (onOffEval_injective A),Module.finrank_prod,
    Module.finrank_fintype_fun_eq_card,Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe,Fintype.card_coe]
/-- Evaluation separately on the two branches permits all state vectors
of size ≤ six on and ≤ four off to be interpolated inside E5. -/
theorem onOffSpace_le_E5 {A : Matrix (Fin s) (Fin s) K} {P : K[X]}
    (hP : ∀ i, g A i≠0 → P.eval (nodes A i)=g A i)
    (hM : (cleanKnots A).card ≤ 6) (hN : (offKnots A).card ≤ 4) :
    onOffSpace A ≤ treeSpace A 5 := by
  rintro _ ⟨z,rfl⟩
  let T := cleanKnots A
  let S := offKnots A
  let f (x : K) : K := if h : x∈T then z.1 ⟨x,h⟩ else 0
  let Q := Lagrange.interpolate T id f
  have hQ : Q.natDegree ≤ 5 := by
    change T.card ≤ 6 at hM
    by_cases h : Q=0
    · simp [h]
    · have hh := (Polynomial.natDegree_lt_iff_degree_lt h).mpr
          (Lagrange.degree_interpolate_lt f (Set.injOn_id _))
      omega
  have heQ (a : K) (ha : a∈T) : Q.eval a=f a :=
    Lagrange.eval_interpolate_at_node f (Set.injOn_id _) ha
  let adjust (x : K) : K := if h : x∈S then (z.2 ⟨x,h⟩-Q.eval x)/P.eval x else 0
  let R := Lagrange.interpolate S id adjust
  have hR : R.natDegree ≤ 3 := by
    change S.card ≤ 4 at hN
    by_cases h : R=0
    · simp [h]
    · have hh := (Polynomial.natDegree_lt_iff_degree_lt h).mpr
          (Lagrange.degree_interpolate_lt adjust (Set.injOn_id _))
      omega
  have heR (a : K) (ha : a∈S) : R.eval a=adjust a :=
    Lagrange.eval_interpolate_at_node adjust (Set.injOn_id _) ha
  have hv : onOffEval A z = evalNodes A Q + diag (g A) (evalNodes A R) := by
    ext i
    by_cases h : g A i=0
    · have hm : nodes A i∈T := mem_cleanKnots.mpr ⟨i,h,rfl⟩
      rw [onOffEval_on A _ h]
      simp [h,heQ _ hm,f,dite_eq_left hm]
    · have hm : nodes A i∈S := mem_offKnots.mpr ⟨i,h,rfl⟩
      rw [onOffEval_off A _ h]
      simp only [Pi.add_apply,evalNodes_apply,diag_apply,heR _ hm,adjust,dite_eq_left hm,hP i h]
      rw [mul_div_cancel₀ _ h]
      ring
  rw [hv]
  exact pairProfile_mem_E5 A Q R hQ hR

/-- The clean tag aggregate of any physical row vector. -/
noncomputable def cleanMass (A : Matrix (Fin s) (Fin s) K) (w : Fin s → K) (x : K) : K :=
  ∑ i, if g A i=0 ∧ nodes A i=x then w i else 0

/-- A physical vector specified independently on the two clock tags. -/
noncomputable def taggedValue (A : Matrix (Fin s) (Fin s) K) (f t : K → K) : Fin s → K :=
  fun i => if g A i=0 then f (nodes A i) else t (nodes A i)

theorem row_taggedValue (A : Matrix (Fin s) (Fin s) K) (w : Fin s → K) (f t : K → K) :
    row w (taggedValue A f t) =
      (∑ x ∈ cleanKnots A, cleanMass A w x * f x) +
        ∑ x ∈ offKnots A, offMass A w x * t x := by
  classical
  have one (i : Fin s) : w i * taggedValue A f t i =
      (∑ x ∈ cleanKnots A, (if g A i=0 ∧ nodes A i=x then w i else 0) * f x) +
        ∑ x ∈ offKnots A, (if g A i≠0 ∧ nodes A i=x then w i else 0) * t x := by
    by_cases hi : g A i=0
    · have hm : nodes A i ∈ cleanKnots A := mem_cleanKnots.mpr ⟨i,hi,rfl⟩
      simp only [taggedValue, if_pos hi, hi, true_and, not_true_eq_false, false_and,
        if_false, zero_mul, Finset.sum_const_zero, add_zero]
      rw [Finset.sum_eq_single (nodes A i)]
      · simp
      · intro x _ hx
        simp [Ne.symm hx]
      · intro h
        exact (h hm).elim
    · have hm : nodes A i ∈ offKnots A := mem_offKnots.mpr ⟨i,hi,rfl⟩
      simp only [taggedValue, if_neg hi, hi, false_and, if_false, zero_mul,
        Finset.sum_const_zero, zero_add, not_false_eq_true, true_and]
      rw [Finset.sum_eq_single (nodes A i)]
      · simp [hi]
      · intro x _ hx
        simp [Ne.symm hx]
      · intro h
        exact (h hm).elim
  simp only [row_apply,dotProduct]
  rw [Finset.sum_congr rfl (fun i _ => one i),Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [cleanMass,Finset.sum_mul]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [offMass,Finset.sum_mul]

theorem row_evalNodes_tag_sum (A : Matrix (Fin s) (Fin s) K) (w : Fin s → K) (P : K[X]) :
    row w (evalNodes A P) =
      (∑ x ∈ cleanKnots A, cleanMass A w x * P.eval x) +
        ∑ x ∈ offKnots A, offMass A w x * P.eval x := by
  have e : evalNodes A P=taggedValue A P.eval P.eval := by
    ext i
    simp [taggedValue]
  rw [e,row_taggedValue]

theorem row_g_profile_tag_sum {A : Matrix (Fin s) (Fin s) K} (w : Fin s → K)
    {P : K[X]} (fit : ∀ i, g A i≠0 → P.eval (nodes A i)=g A i) (V : K[X]) :
    row w (diag (g A) (evalNodes A V)) =
      ∑ x ∈ offKnots A, offMass A w x * (P.eval x * V.eval x) := by
  have e : diag (g A) (evalNodes A V)=taggedValue A (fun _ => 0) (fun x => P.eval x*V.eval x) := by
    ext i
    by_cases hi : g A i=0
    · simp [taggedValue,hi]
    · simp [taggedValue,hi,fit i hi]
  rw [e,row_taggedValue]
  simp

theorem cleanMass_singleton {A : Matrix (Fin s) (Fin s) K} (w : Fin s → K)
    {i : Fin s} (hi : g A i=0)
    (unique : ∀ j, g A j=0 → nodes A j=nodes A i → j=i) :
    cleanMass A w (nodes A i)=w i := by
  classical
  unfold cleanMass
  rw [Finset.sum_eq_single i]
  · simp [hi]
  · intro j _ ne
    have test : ¬ (g A j=0 ∧ nodes A j=nodes A i) := fun h => ne (unique j h.1 h.2)
    simp [test]
  · simp

end Tags

section ActualRank

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

private theorem origin_data (ha : ∀ i j, i ≤ j → A i j=0) :
    g A 0=0 ∧ nodes A 0=0 := by
  have v0 (v : Fin 10 → K) : mat A v 0=0 :=
    causal_mat ha 0 v (fun j hj => ((not_lt_of_ge (Fin.zero_le j)) hj).elim)
  have c0 : nodes A 0=0 := by simpa [mat_apply,nodes] using v0 (1 : Fin 10 → K)
  refine ⟨?_,c0⟩
  rw [g_apply,c0,v0]
  simp

private theorem clean_mass_paid_nonzero (ho : HasOrder 8 A b)
    (hM : (cleanKnots A).card=5) (h1 : (1:K)∈cleanKnots A)
    (terminal : cleanMass A b 1 ≠ 0) (cancel : ∀ x ∈ offKnots A, offMass A b x=0) :
    ∀ x ∈ cleanKnots A, cleanMass A b x ≠ 0 := by
  classical
  intro x hx x0
  have xn : x≠1 := fun e => terminal (e ▸ x0)
  let T := ((cleanKnots A).erase 1).erase x
  have c1 := Finset.card_erase_add_one h1
  have cx : T.card+1=((cleanKnots A).erase 1).card :=
    Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨xn,hx⟩)
  let D := nodalHull T
  let Q := (1-X)*D^2
  have dD : D.natDegree=3 := by rw [show D.natDegree=T.card from natDegree_nodalHull T]; omega
  have hD : D ≠ 0 := (monic_nodalHull T).ne_zero
  have d1 : ((1-X):K[X]).natDegree≤1 :=
    (natDegree_sub_le (1 : K[X]) (X : K[X])).trans
      (by rw [natDegree_one,natDegree_X] <;> decide)
  have d2 : (D^2).natDegree≤6 := by
    rw [pow_two]
    exact natDegree_mul_le_of_le dD.le dD.le
  have de : Q.natDegree≤7 := natDegree_mul_le_of_le d1 d2
  have pos : 0 < (primitive Q).eval 1 := by
    rw [←formalPrimitive_eq_native Q]
    simpa [Q] using (RKCert.ReviewedNative.UnitBetaSquareMass.beta_square_pos 0 1 hD)
  have z : row b (evalNodes A Q)=0 := by
    rw [row_evalNodes_tag_sum]
    have zr : (∑ y ∈ offKnots A, offMass A b y*Q.eval y)=0 := by
      apply Finset.sum_eq_zero
      intro y hy
      rw [cancel y hy,zero_mul]
    rw [zr,add_zero]
    apply Finset.sum_eq_zero
    intro y hy
    by_cases y1 : y=1
    · subst y
      simp [Q]
    by_cases yx : y=x
    · subst y
      simp [x0]
    have memT : y∈T := Finset.mem_erase.mpr ⟨yx,Finset.mem_erase.mpr ⟨y1,hy⟩⟩
    have vD : D.eval y=0 := nodalHull_eval_of_mem memT
    simp [Q,vD]
  have paid := probe_evalNodes ho Q 0 (by omega)
  simp only [probe,pow_zero,mul_one,one_mul] at paid
  exact (ne_of_gt pos) (paid.symm.trans z)

/-- All rank and tag facts used for physical localization, obtained from the
measured census and actual order; P is the actual common off profile. -/
structure RankData (A : Matrix (Fin 10) (Fin 10) K) (b : Fin 10 → K) (P : K[X]) : Prop where
  horizon : ERKEvenHorizon A b 4
  headDegree : P.natDegree≤2
  headNonzero : P≠0
  bandThree : zeroSpace A 3=band A 1
  bandFour : zeroSpace A 4=band A 2
  fit : ∀ i, g A i≠0 → P.eval (nodes A i)=g A i
  offCard : (offKnots A).card=4
  cleanCard : (cleanKnots A).card=5
  cancel : ∀ x ∈ offKnots A, offMass A b x=0
  treeFive : treeSpace A 5=onOffSpace A
  rankFive : finrank K (treeSpace A 5)=9
  liveNine : b 9≠0
  clockNine : nodes A 9=1
  unitNine : coordinate (K:=K) (9 : Fin 10) ∈ treeSpace A 4
  cleanNine : g A 9=0
  uniqueOne : ∀ i, g A i=0 → nodes A i=1 → i=9
  cleanZero : g A 0=0
  clockZero : nodes A 0=0
  cleanMassNe : ∀ x ∈ cleanKnots A, cleanMass A b x≠0

theorem rankData_of_order8_four_off (ha : ∀ i j, i ≤ j → A i j=0)
    (ho : HasOrder 8 A b) (off : (offKnots A).card=4) : ∃ P, RankData A b P := by
  obtain ⟨H,hcases⟩ := MultiOff.order8_native_tagged_census ha ho
  have hc5 : (cleanKnots A).card=5 := by
    rcases hcases with one | ⟨_,hc5⟩
    · omega
    · exact hc5
  obtain ⟨r3,r4,_,_⟩ := forward_minimal_ranks ha ho (by decide) (by simpa using H.treeRank.le)
  obtain ⟨P,dP,Pn,B3,B4,fit⟩ := two_curve_head r3 r4 (by omega)
  have cancel : ∀ x ∈ offKnots A, offMass A b x=0 :=
    offMass_zero_of_head ho fit (by omega)
  have wle := onOffSpace_le_E5 fit (by omega) (by omega)
  have w9 : finrank K (onOffSpace A)=9 := by
    rw [onOffSpace_rank,hc5,off]
  have back := backward_count ha ho 5 1 (by decide)
  have cap : finrank K (treeSpace A 5)≤9 := by omega
  have tree : onOffSpace A=treeSpace A 5 :=
    Submodule.eq_of_le_of_finrank_le wle (by omega)
  have rank : finrank K (treeSpace A 5)=9 := by rw [←tree,w9]
  obtain ⟨t,tmax,tLive,tClock,tUnit⟩ := H.terminal
  have ht : t=Fin.last 9 := le_antisymm (Fin.le_last t) (tmax (Fin.last 9))
  subst t
  have b9 : b 9≠0 := tLive.live
  have c9 : nodes A 9=1 := tClock
  have e9 : coordinate (K:=K) (9 : Fin 10)∈treeSpace A 4 := tUnit
  have w9mem : coordinate (K:=K) (9 : Fin 10)∈onOffSpace A := by
    rw [tree]
    exact treeSpace_mono A (by decide : 4≤5) e9
  have g9 : g A 9=0 := by
    apply on_of_state_single _ b9 cancel
    simpa only [coordinate_as_single] using w9mem
  have only1 (i : Fin 10) (gi : g A i=0) (ci : nodes A i=1) : i=9 := by
    by_contra ne
    have eq := onOffSpace_apply_eq w9mem (show SameTag A i 9 from
      ⟨ci.trans c9.symm,iff_of_true gi g9⟩)
    simp [coordinate_as_single,ne] at eq
  have M1 : cleanMass A b 1=b 9 := by
    rw [←c9]
    exact cleanMass_singleton b g9 (fun i gi ci => only1 i gi (ci.trans c9))
  have h1 : (1:K)∈cleanKnots A := mem_cleanKnots.mpr ⟨9,g9,c9⟩
  obtain ⟨g0,c0⟩ := origin_data ha
  exact ⟨P, H,dP,Pn,B3,B4,fit,off,hc5,cancel,tree.symm,rank,b9,c9,e9,g9,only1,g0,c0,
    clean_mass_paid_nonzero ho hc5 h1 (fun z => b9 (M1.symm.trans z)) cancel⟩

end ActualRank
end RKResearch.Certified.Graded.FourOffPhysical
