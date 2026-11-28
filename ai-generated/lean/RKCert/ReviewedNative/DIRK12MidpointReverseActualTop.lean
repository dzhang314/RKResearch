module

public import RKCert.ReviewedNative.DIRK12MidpointForwardActualNodal
public import RKCert.ReviewedNative.DIRK12MidpointReverseThreeSpan
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! Pay the true fifth reverse primitive and the true transpose image
of the barycentric mode. Both are literal vectors of the same real
15-stage tableau. No expanded local quartic gate or numerical rank is
needed: the degree-six nodal fit and the seven-site rank suffice. -/
namespace RKResearch.Certified.DIRK12MidpointReverse.Actual

open RKResearch Graded Polynomial
open DIRK12MidpointForward DIRK12MidpointForward.Opening DIRK12MidpointRealInterval DirectedRatBox
open DIRK12MidpointProbes DIRK12MidpointShape
open scoped Matrix BigOperators Polynomial

section Actual
variable (x f : ℝ)
local notation "F" => (assembled x f)
local notation "Areal" => (Feed.tableau (assembled x f))
local notation "Breal" => (Feed.b (assembled x f))
local notation "Cphys" => (nodes Areal)
local notation "Yphys" => ((1:V15 ℝ)-Cphys)
local notation "W" => (DualSupport12.moment Areal Breal)
local notation "G" => (profileG x f)
local notation "H" => (profileH x f)
local notation "X5" => (DualSupport12.reverse Areal Breal 4)
local notation "NH" => (mat (Matrix.transpose Areal) H)

theorem ghost_is_hidden (i : Fin 15) (hi : ghostRow i) :
    ∃ g : Fin 4, i=DIRK12MidpointForward.hidden g := by
  have h : 1 ≤ i.val ∧ i.val ≤ 4 := hi
  let g : Fin 4 := ⟨i.val-1,by omega⟩
  refine ⟨g,Fin.ext ?_⟩
  rw [hidden_val]
  change i.val=i.val-1+1
  omega

theorem replace_nonterminal_read (z v w : V15 ℝ)
    (zg : ∀ i, ghostRow i → z i=0) (zt : z terminal=0)
    (same : ∀ i, ¬ ghostRow i → i≠terminal → v i=w i) :
    row z v=row z w := by
  simp only [row_apply,dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  by_cases g : ghostRow i
  · rw [zg i g,zero_mul,zero_mul]
  · by_cases t : i=terminal
    · rw [t,zt,zero_mul,zero_mul]
    · rw [same i g t]

noncomputable def physicalGhostTapPoly (g : Fin 4) : ℝ[X] :=
  (DIRK12MidpointGhost.tap g:ℝ) •
    (alpha x (yOf x) • shape 0+
      (mu x (yOf x)+nu x*(F).clocks (DIRK12MidpointForward.hidden g)) • shape 1+
      gammaFrom (alpha x (yOf x)) • shape 2)

theorem physicalGhostTap_degree (g : Fin 4) :
    (physicalGhostTapPoly x f g).natDegree≤7 := by
  unfold physicalGhostTapPoly
  refine (Polynomial.natDegree_smul_le _ _).trans ?_
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (Polynomial.natDegree_smul_le _ _).trans ((shape_degree 0).trans (by decide))
    · exact (Polynomial.natDegree_smul_le _ _).trans ((shape_degree 1).trans (by decide))
  · exact (Polynomial.natDegree_smul_le _ _).trans ((shape_degree 2).trans (by decide))

theorem literal_ghost_column (g : Fin 4) (i : Fin 15)
    (hi : ¬ghostRow i) (nt : i≠terminal) :
    Areal i (DIRK12MidpointForward.hidden g)=
      Vector.evalVector Yphys (physicalGhostTapPoly x f g) i := by
  revert hi nt
  refine stage_cases (P:=fun i => ¬ghostRow i → i≠terminal →
      Areal i (DIRK12MidpointForward.hidden g)=
        Vector.evalVector Yphys (physicalGhostTapPoly x f g) i) ?_ ?_ ?_ i
  · intro _ _
    rw [(F).tableau_origin]
    simp only [physicalGhostTapPoly,map_smul,map_add,profile_shape_eval,
      Pi.smul_apply,Pi.add_apply,smul_eq_mul]
    simp [actualProfile,(F).nodes_tableau]
  · intro k e _
    exact (e (ghost_hidden k)).elim
  · intro k _ e
    rw [(F).tableau_nonterminal_tap k g e,Feed.ghostTap]
    simp only [physicalGhostTapPoly,map_smul,map_add,profile_shape_eval,Pi.smul_apply,
      Pi.add_apply,smul_eq_mul]
    simp only [actualProfile,(F).nodes_tableau,Feed.clocks_visible]
    change _*((F).mode0 k+(F).mode1 k*(F).clocks (DIRK12MidpointForward.hidden g))=_
    change _*(realClock x f k*(alpha x (yOf x)*leg5 (realClock x f k)+
        mu x (yOf x)*leg6 (realClock x f k)+
        gammaFrom (alpha x (yOf x))*leg7 (realClock x f k))+
      (realClock x f k*nu x*leg6 (realClock x f k))*(F).clocks (DIRK12MidpointForward.hidden g))=_
    rw [show (F).cVisible k=realClock x f k by rfl]
    congr 1
    norm_num [leg]
    ring

section Roots
variable (hx : Encloses xBox x) (hf : Encloses fBox f)
    (hx0 : realX x=0) (hf0 : realF x f=0)
include hx hf hx0 hf0

theorem forward_fourth_probe (m : Nat) (hm : m≤5) :
    row (W 4) (DualSupport12.forward Areal m)=0 := by
  by_cases sm : m < 5
  · have p := fw_support (m+1) _ (assembled_fw_primitive x f hx hf hx0 hf0 m sm)
    rw [replace_positive_read x f 4 (by decide) _ (0:V15 ℝ) (fun i hi _ => p i hi)]
    simp
  · have t : m=5 := by omega
    subst m
    rw [replace_positive_read x f 4 (by decide) _
      (quinticScale x • actualProfile Areal 1)
      (actual_quintic_profile x f hx hf hx0 hf0)]
    have p := profile_probe Areal Breal (assembled_quad x f hx hf hx0 hf0) 1 (4:Fin 7)
      (by decide) (by decide)
    rw [ite_eq_right (by decide : (4:Fin 7)≠0)] at p
    change row (W 4) (actualProfile Areal 1)=0 at p
    rw [map_smul,smul_eq_mul,p,mul_zero]

theorem reverse_five_low_silent (m : Nat) (hm : m≤5) :
    row X5 (Cphys^m)=0 := by
  have p := DualSupport12.mixed_scalar Areal Breal (assembled_scalar x f hx hf hx0 hf0)
    4 m (by omega)
  change ((m+1:Nat):ℝ)*row (W 5) (Cphys^m)=5*row (W 4) (Cphys^(m+1)) at p
  have s : ((m+1:Nat):ℝ)*row X5 (Cphys^m)=
      5*row (W 4) (DualSupport12.forward Areal m) := by
    rw [DualSupport12.reverse,Vector.left_sub,Vector.left_smul,←Vector.transpose_read,
      DualSupport12.forward,map_sub,map_smul,smul_eq_mul]
    change ((m+1:Nat):ℝ)*(5*row (W 4) (mat Areal (Cphys^m))-row (W 5) (Cphys^m))=
      5*(((m+1:Nat):ℝ)*row (W 4) (mat Areal (Cphys^m))-row (W 4) (Cphys^(m+1)))
    linear_combination -p
  rw [forward_fourth_probe x f hx hf hx0 hf0 m hm,mul_zero] at s
  exact (mul_eq_zero.mp s).resolve_left (Nat.cast_ne_zero.mpr (by omega))

theorem reverse_five_nodal_silent : row X5 (nodalInput x f)=0 := by
  have p := actual_nodal_fourth_read x f hx hf hx0 hf0
  have a := scalar_fromOne_moment Areal Breal (assembled_quad x f hx hf hx0 hf0)
    4 (openingNodal x f) (by rw [openingNodal_degree]; decide)
  change row (W 4) (Vector.evalVector Yphys (fromOne (openingNodal x f)))=
    row (W 5) (nodalInput x f)/(5:ℝ) at a
  rw [DualSupport12.reverse,Vector.left_sub,Vector.left_smul,←Vector.transpose_read,p,a]
  change 5*(row (W 5) (nodalInput x f)/5)-row (W 5) (nodalInput x f)=0
  ring

theorem reverse_five_silent (m : Nat) (hm : m≤6) :
    row X5 (Cphys^m)=0 := by
  by_cases e : m=6
  · subst m
    exact Vector.power_from_top Cphys (row X5) 6 (by decide) (openingNodal x f)
      (nodal_monic x f) (openingNodal_degree x f)
      (fun j hj => reverse_five_low_silent x f hx hf hx0 hf0 j (by omega))
      (reverse_five_nodal_silent x f hx hf hx0 hf0)
  · exact reverse_five_low_silent x f hx hf hx0 hf0 m (by omega)

theorem reverse_five_ghost (i : Fin 15) (g : ghostRow i) : X5 i=0 := by
  obtain ⟨k,e⟩ := ghost_is_hidden i g
  subst i
  have h := assembled_reverse_ghost x f hx hf hx0 hf0 k (3:Fin 4)
  change mat (Matrix.transpose Areal) (W 4) (DIRK12MidpointForward.hidden k)=0 at h
  change (5:ℝ)*mat (Matrix.transpose Areal) (W 4) (DIRK12MidpointForward.hidden k)-
      W 5 (DIRK12MidpointForward.hidden k)=0
  rw [h]
  simp [DualSupport12.moment,assembled_ghost_zero]

omit hx0 hf0 in
theorem physical_terminal_image (z : V15 ℝ) :
    mat (Matrix.transpose Areal) z terminal=0 := by
  change (∑ i, Areal i terminal*z i)=0
  apply Finset.sum_eq_zero
  intro i _
  have e : Areal i terminal=0 :=
    Physical.terminal_column (zeroHead x f) (exactData x f) (assembled_geom x f hx hf) i
  rw [e,zero_mul]

omit hx0 hf0 in
theorem reverse_five_terminal : X5 terminal=0 := by
  change (5:ℝ)*mat (Matrix.transpose Areal) (W 4) terminal-W 5 terminal=0
  rw [physical_terminal_image x f hx hf]
  simp [DualSupport12.moment,DualSupport12.reflected,assembled_node_terminal x f]

theorem reverse_five_three :
    ∃ a b c : ℝ, X5=a • G+b • H+c • (Yphys*H) :=
  annihilator_three x f hx hf X5 (reverse_five_ghost x f hx hf hx0 hf0)
    (reverse_five_terminal x f hx hf) (reverse_five_silent x f hx hf hx0 hf0)

theorem H_forward_defect_silent (m : Nat) (hm : m≤5) :
    row H (DualSupport12.forward Areal m)=0 := by
  by_cases sm : m < 5
  · have p := fw_support (m+1) _ (assembled_fw_primitive x f hx hf hx0 hf0 m sm)
    rw [replace_nonterminal_read H _ (0:V15 ℝ) (H_zero_ghost x f hx hf)
      (H_zero_terminal x f hx hf) (fun i hi _ => p i hi)]
    simp
  · have t : m=5 := by omega
    subst m
    rw [replace_nonterminal_read H _ (quinticScale x • actualProfile Areal 1)
      (H_zero_ghost x f hx hf) (H_zero_terminal x f hx hf)
      (actual_quintic_profile x f hx hf hx0 hf0),map_smul,smul_eq_mul,
      ←profile_shape_eval]
    have q := Vector.silent_reflected Cphys H (shape 1) 7
      ((shape_degree 1).trans (by decide))
      (actual_H_silent x f hx hf)
    rw [q,mul_zero]

theorem H_image_low_silent (m : Nat) (hm : m≤5) :
    row H (mat Areal (Cphys^m))=0 := by
  have h := H_forward_defect_silent x f hx hf hx0 hf0 m hm
  rw [DualSupport12.forward,map_sub,map_smul,smul_eq_mul,
    actual_H_silent x f hx hf (m+1) (by omega),sub_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (Nat.cast_ne_zero.mpr (by omega))

theorem H_image_nodal_silent : row H (mat Areal (nodalInput x f))=0 := by
  rw [replace_nonterminal_read H _ _ (H_zero_ghost x f hx hf)
    (H_zero_terminal x f hx hf) (actual_nodal_image x f hx hf hx0 hf0)]
  exact Vector.silent_reflected Cphys H (nodalImage x f) 7 (nodal_image_degree x f)
    (actual_H_silent x f hx hf)

theorem transpose_H_silent (m : Nat) (hm : m≤6) :
    row NH (Cphys^m)=0 := by
  rw [←Vector.transpose_read]
  by_cases e : m=6
  · subst m
    exact Vector.power_from_top Cphys ((row H).comp (mat Areal)) 6 (by decide)
      (openingNodal x f) (nodal_monic x f) (openingNodal_degree x f)
      (fun j hj => H_image_low_silent x f hx hf hx0 hf0 j (by omega))
      (H_image_nodal_silent x f hx hf hx0 hf0)
  · exact H_image_low_silent x f hx hf hx0 hf0 m (by omega)

omit hx0 hf0 in
theorem transpose_H_ghost (i : Fin 15) (hg : ghostRow i) : NH i=0 := by
  obtain ⟨g,e⟩ := ghost_is_hidden i hg
  subst i
  have h :
      NH (DIRK12MidpointForward.hidden g)=
        row H (fun i => Areal i (DIRK12MidpointForward.hidden g)) := by
    change (∑ i, Areal i (DIRK12MidpointForward.hidden g)*H i)=∑ i, H i*Areal i (DIRK12MidpointForward.hidden g)
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h,replace_nonterminal_read H _ _ (H_zero_ghost x f hx hf)
    (H_zero_terminal x f hx hf) (fun i g' t' => literal_ghost_column x f g i g' t')]
  exact Vector.silent_reflected Cphys H (physicalGhostTapPoly x f g) 7
    (physicalGhostTap_degree x f g) (actual_H_silent x f hx hf)

theorem transpose_H_three :
    ∃ a b c : ℝ, NH=a • G+b • H+c • (Yphys*H) :=
  annihilator_three x f hx hf NH (transpose_H_ghost x f hx hf)
    (physical_terminal_image x f hx hf H) (transpose_H_silent x f hx hf hx0 hf0)

end Roots
end Actual
end RKResearch.Certified.DIRK12MidpointReverse.Actual

#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.reverse_five_silent
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.reverse_five_three
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.transpose_H_silent
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.transpose_H_three
