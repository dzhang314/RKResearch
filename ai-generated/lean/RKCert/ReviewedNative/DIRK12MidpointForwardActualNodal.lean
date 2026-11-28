module

public import RKCert.ReviewedNative.DIRK12MidpointForwardActualLow
public import RKCert.ReviewedNative.DIRK12MidpointNodalFourthProbe
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! The true image of the reflected degree-six opening nodal input.
The five ordinary opening rows read only the paid literal ghost taps;
three paid adjoint pairings extend that image to all nonterminal
ordinary rows. A fourth, still degree-eleven paid probe checks the
last reverse primitive without expanding five quartic local equations. -/
namespace RKResearch.Certified.DIRK12MidpointReverse.Actual

open RKResearch Graded Polynomial
open DIRK12MidpointForward DIRK12MidpointForward.Opening DIRK12MidpointForward.Late
open DIRK12MidpointRealInterval DirectedRatBox DIRK12MidpointProbes DIRK12MidpointShape
open scoped Matrix BigOperators Polynomial

section Actual

variable (x f : ℝ)
local notation "F" => (assembled x f)
local notation "Areal" => (Feed.tableau (assembled x f))
local notation "Breal" => (Feed.b (assembled x f))
local notation "Cphys" => (nodes Areal)
local notation "Yphys" => ((1:V15 ℝ)-Cphys)
local notation "W" => (DualSupport12.moment Areal Breal)
local notation "ByY" => (Vector.evalVector Yphys)
local notation "Qnod" => (openingNodal x f)

noncomputable def nodalInput : V15 ℝ := ByY Qnod

noncomputable def ghostRead0 : ℝ :=
  ∑ g : Fin 4, (DIRK12MidpointGhost.tap g:ℝ)*nodalInput x f (DIRK12MidpointForward.hidden g)

noncomputable def ghostRead1 : ℝ :=
  ∑ g : Fin 4, (DIRK12MidpointGhost.tap g:ℝ)*(F).clocks (DIRK12MidpointForward.hidden g)*
    nodalInput x f (DIRK12MidpointForward.hidden g)

noncomputable def ghostFitCoeffs : Fin 3 → ℝ :=
  ![alpha x (yOf x)*ghostRead0 x f,
    mu x (yOf x)*ghostRead0 x f+nu x*ghostRead1 x f,
    gammaFrom (alpha x (yOf x))*ghostRead0 x f]

noncomputable def ghostFit : ℝ[X] :=
  ∑ d : Fin 3, ghostFitCoeffs x f d • shape d

/-- The complete nonterminal ordinary polynomial image A Qnod. -/
noncomputable def nodalImage : ℝ[X] :=
  nodalTarget x f+fromOne Qnod+ghostFit x f

theorem ghost_fit_degree : (ghostFit x f).natDegree≤7 := by
  unfold ghostFit
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d _
  have t := shape_degree d
  exact (Polynomial.natDegree_smul_le _ _).trans (by have e := d.isLt; omega)

theorem nodal_image_degree : (nodalImage x f).natDegree≤7 := by
  unfold nodalImage
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (ghost_fit_degree x f))
  refine (Polynomial.natDegree_add_le _ _).trans (max_le (nodalTarget_degree x f) ?_)
  exact (fromOne_degree Qnod).trans (by rw [openingNodal_degree])

theorem nodal_monic : (Qnod).Monic := hull_monic _

private theorem hull_eval_mem (s : List ℝ) (v : ℝ) (hv : v∈s) :
    (hull s).eval v=0 := by
  induction s with
  | nil => simp at hv
  | cons a s ih =>
    rw [hull,eval_mul,eval_sub,eval_X,eval_C]
    rcases List.mem_cons.mp hv with e|h
    · rw [e,sub_self,zero_mul]
    · rw [ih h,mul_zero]

theorem nodal_site_zero (k : Fin 6) : (Qnod).eval (site x f (Fin.castAdd 3 k).succ)=0 := by
  apply hull_eval_mem
  have e : site x f (Fin.castAdd 3 k).succ=(fixed x f).tail.get k := by
    fin_cases k <;> rfl
  rw [e]
  exact List.get_mem _ _

theorem nodal_input_origin : nodalInput x f 0=0 := by
  have c := assembled_real_nodes x f 0 (by decide)
  change (1:ℝ)-Cphys 0=site x f ((Fin.castAdd 3 (0:Fin 6)).succ) at c
  change (Qnod).eval (1-Cphys 0)=0
  rw [c]
  exact nodal_site_zero x f 0

theorem nodal_input_head (j : Fin 5) :
    nodalInput x f (visible (Physical.head j))=0 := by
  have h := assembled_real_nodes x f (visible (Physical.head j))
    (non_ghost_visible (Physical.head j))
  change (Qnod).eval (1-Cphys (visible (Physical.head j)))=0
  rw [h]
  have tag : stageTag (visible (Physical.head j))=(Fin.castAdd 3 j.succ).succ := by
    fin_cases j <;> decide
  rw [tag]
  exact nodal_site_zero x f j.succ

theorem profile_shape_eval (d : Fin 3) : ByY (shape d)=actualProfile Areal d := by
  funext i
  change (shape d).eval (1-Cphys i)=Cphys i*leg d (Cphys i)
  exact shape_eval d (Cphys i)

theorem evaluated_ghost_fit :
    ByY (ghostFit x f)=∑ d : Fin 3, ghostFitCoeffs x f d • actualProfile Areal d := by
  rw [ghostFit,map_sum]
  simp only [map_smul,profile_shape_eval]

private theorem image_input_root (i : Fin 15) (h : nodalInput x f i=0) :
    ByY (nodalImage x f) i=ByY (ghostFit x f) i := by
  unfold nodalImage nodalTarget
  rw [sub_add_cancel]
  simp only [Vector.at_apply,eval_add,Polynomial.smul_eq_C_mul,eval_mul,eval_C]
  change (Qnod).eval (Yphys i)=0 at h
  rw [h,mul_zero,mul_zero,zero_add]

theorem nodal_image_origin :
    mat Areal (nodalInput x f) 0=ByY (nodalImage x f) 0 := by
  rw [image_input_root x f 0 (nodal_input_origin x f),evaluated_ghost_fit]
  change (∑ i : Fin 15, Areal 0 i*nodalInput x f i)=_
  simp [(F).tableau_origin,actualProfile,(F).nodes_tableau]

theorem literal_ghost_input (i : Fin 10) (hi : visible i≠terminal) :
    (∑ g : Fin 4, Areal (visible i) (DIRK12MidpointForward.hidden g)*
      nodalInput x f (DIRK12MidpointForward.hidden g))=
      ByY (ghostFit x f) (visible i) := by
  have split (g : Fin 4) :
      Areal (visible i) (DIRK12MidpointForward.hidden g)*nodalInput x f (DIRK12MidpointForward.hidden g)=
        (F).mode0 i*((DIRK12MidpointGhost.tap g:ℝ)*nodalInput x f (DIRK12MidpointForward.hidden g))+
        (F).mode1 i*((DIRK12MidpointGhost.tap g:ℝ)*(F).clocks (DIRK12MidpointForward.hidden g)*
            nodalInput x f (DIRK12MidpointForward.hidden g)) := by
    rw [(F).tableau_nonterminal_tap i g hi,Feed.ghostTap]
    ring
  simp_rw [split]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,evaluated_ghost_fit]
  change (F).mode0 i*ghostRead0 x f+(F).mode1 i*ghostRead1 x f=_
  rw [Finset.sum_apply,Fin.sum_univ_three]
  simp only [Pi.smul_apply,smul_eq_mul,actualProfile,(F).nodes_tableau,Feed.clocks_visible]
  change realClock x f i*(alpha x (yOf x)*leg5 (realClock x f i)+
        mu x (yOf x)*leg6 (realClock x f i)+
        gammaFrom (alpha x (yOf x))*leg7 (realClock x f i))*ghostRead0 x f+
      (realClock x f i*nu x*leg6 (realClock x f i))*ghostRead1 x f=_
  rw [show (F).cVisible i=realClock x f i by rfl]
  norm_num [ghostFitCoeffs,leg]
  ring

theorem nodal_image_head (j : Fin 5) :
    mat Areal (nodalInput x f) (visible (Physical.head j))=
      ByY (nodalImage x f) (visible (Physical.head j)) := by
  rw [image_input_root x f _ (nodal_input_head x f j)]
  change (∑ i : Fin 15, Areal (visible (Physical.head j)) i*nodalInput x f i)=_
  rw [sum_stages,nodal_input_origin,mul_zero,zero_add]
  have e : (∑ i : Fin 10, Areal (visible (Physical.head j)) (visible i)*
      nodalInput x f (visible i))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases h : j.val < i.val
    · have e : visible (Physical.head j)<visible i := by
        change (visible (Physical.head j)).val < (visible i).val
        simp only [visible_val,Physical.head_val]
        omega
      have q : Areal (visible (Physical.head j)) (visible i)=0 := (F).isLower e
      rw [q,zero_mul]
    · let k : Fin 5 := ⟨i.val,by omega⟩
      have e : Physical.head k=i := Fin.ext rfl
      rw [←e,nodal_input_head,mul_zero]
  rw [e,add_zero]
  have ne : visible (Physical.head j)≠terminal := by
    intro eq
    have h := congrArg Fin.val eq
    simp only [visible_val,Physical.head_val,Fin.val_last] at h
    omega
  exact literal_ghost_input x f _ ne

section Roots
variable (hx : Encloses xBox x) (hf : Encloses fBox f) (hx0 : realX x=0) (hf0 : realF x f=0)

include hx hf in
theorem nodal_image_pair :
    mat Areal (nodalInput x f) 11=mat Areal (nodalInput x f) 13 := by
  have g := assembled_geom x f hx hf
  have hs : row (profileH x f) (nodalInput x f)=0 :=
    Vector.silent_reflected Cphys _ Qnod 7 (by rw [openingNodal_degree]; decide)
      (actual_H_silent x f hx hf)
  have equal := Physical.same_seed_clocks _ _ g
  change Cphys 11=Cphys 13 at equal
  have p : nodalInput x f 11=nodalInput x f 13 := by
    change (Qnod).eval (1-Cphys 11)=(Qnod).eval (1-Cphys 13)
    rw [equal]
  exact paired_read_equal Areal (Physical.paired _ _) (d x f/2) (profileH x f)
    (nodalInput x f) (Physical.paired_nz _ _ g) p hs (actual_pair_identity x f hx hf)

include hx hf hx0 hf0

theorem candidate_nodal_read (j : Fin 4) :
    row (W (j.val+1)) (ByY (nodalImage x f))=
      row (W (j.val+1)) (ByY (fromOne Qnod)) := by
  have e := actual_nodal_all_four hx hf hx0 hf0 Areal (assembled_real_nodes x f) j
  change row (W (j.val+1)) (ByY (nodalTarget x f))=0 at e
  have s := probe_combo_positive Areal Breal (assembled_quad x f hx hf hx0 hf0)
      (ghostFitCoeffs x f) j
  rw [←evaluated_ghost_fit x f] at s
  rw [nodalImage,map_add,map_add,map_add,map_add,e,s,zero_add,add_zero]

theorem nodal_already_paid (j : Fin 3) :
    row (W (j.val+1)) (mat Areal (nodalInput x f))=
      row (W (j.val+1)) (ByY (fromOne Qnod)) := by
  let k := j.val+1
  have q : row (DualSupport12.reverse Areal Breal k) (nodalInput x f)=0 :=
    Vector.silent_reflected Cphys _ Qnod 7 (by rw [openingNodal_degree]; decide)
      (reverse_low_silent x f hx hf hx0 hf0 j)
  rw [DualSupport12.reverse,Vector.left_sub,Vector.left_smul,←Vector.transpose_read] at q
  have nz : ((k+1:Nat):ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have a : row (W k) (mat Areal (nodalInput x f))=row (W (k+1)) (nodalInput x f)/((k+1:Nat):ℝ) := by
    apply (eq_div_iff nz).2
    linear_combination q
  exact a.trans (scalar_fromOne_moment Areal Breal (assembled_quad x f hx hf hx0 hf0) k Qnod
    (by rw [openingNodal_degree]; dsimp [k]; omega)).symm

theorem actual_nodal_image (i : Fin 15) (hi : ¬ghostRow i) (ht : i≠terminal) :
    mat Areal (nodalInput x f) i=ByY (nodalImage x f) i := by
  let z := mat Areal (nodalInput x f)
  let v := ByY (nodalImage x f)
  let w := z-v
  have o : w 0=0 := sub_eq_zero.mpr (nodal_image_origin x f)
  have h (j : Fin 5) : w (visible (Physical.head j))=0 :=
    sub_eq_zero.mpr (nodal_image_head x f j)
  have p : w 11=w 13 := by
    have e := nodal_image_pair x f hx hf
    have a := Physical.same_seed_clocks _ _ (assembled_geom x f hx hf)
    change Cphys 11=Cphys 13 at a
    change mat Areal (nodalInput x f) 11-(nodalImage x f).eval (1-Cphys 11)=
      mat Areal (nodalInput x f) 13-(nodalImage x f).eval (1-Cphys 13)
    rw [e,a]
  have s (j : Fin 3) : row (W (j.val+1)) w=0 := by
    let k : Fin 4 := ⟨j.val,by omega⟩
    change row (W (j.val+1)) (z-v)=0
    rw [map_sub]
    exact sub_eq_zero.mpr ((nodal_already_paid x f hx hf hx0 hf0 j).trans
      (candidate_nodal_read x f hx hf hx0 hf0 k).symm)
  have ⟨a,b,c,d⟩ := assembled_late_profile x f hx hf w (early_weighted x f w o h) p s
  exact sub_eq_zero.mp (nonghost_nonterminal_cases (Q:=fun i => w i=0) o h a b c d i hi ht)

omit hx hf hx0 hf0 in
theorem replace_positive_read (j : Nat) (hj : 0 < j) (v w : V15 ℝ)
    (same : ∀ i, ¬ghostRow i → i≠terminal → v i=w i) :
    row (W j) v=row (W j) w := by
  simp only [row_apply,dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : ghostRow i
  · have z : Breal i=0 := by
      change physicalWeight x f i=0
      rw [physicalWeight,ite_eq_left h]
    simp [DualSupport12.moment,z]
  · by_cases hT : i=terminal
    · subst i
      have e : DualSupport12.reflected Areal terminal=0 := by
        change 1-Cphys terminal=0
        rw [assembled_node_terminal x f,sub_self]
      simp [DualSupport12.moment,e,zero_pow hj.ne']
    · rw [same i h hT]

/-- The actual primitive's final paid scalar test. This is not a
moment of a guessed image: the literal late rows have already been fitted. -/
theorem actual_nodal_fourth_read :
    row (W 4) (mat Areal (nodalInput x f))=
      row (W 4) (ByY (fromOne Qnod)) := by
  rw [replace_positive_read x f 4 (by decide) _ _
      (actual_nodal_image x f hx hf hx0 hf0)]
  exact candidate_nodal_read x f hx hf hx0 hf0 (3:Fin 4)

end Roots
end Actual
end RKResearch.Certified.DIRK12MidpointReverse.Actual

#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.nodal_image_head
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.nodal_image_degree
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.actual_nodal_image
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.actual_nodal_fourth_read
