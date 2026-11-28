module

public import RKCert.ReviewedNative.DIRK12MidpointReverseActualLow
public import RKCert.ReviewedNative.DIRK12MidpointRealLateCompletion
public import RKCert.ReviewedNative.DIRK12MidpointGhostImageBridge
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

@[expose] public section

/-! Complete the ordinary physical forward primitives and the true
entering-quintic profile of the assembled real width-fifteen tableau.
All three late probes are now actual reverse primitives, not assumptions. -/
namespace RKResearch.Certified.DIRK12MidpointReverse.Actual

open RKResearch Graded DIRK12MidpointForward DIRK12MidpointForward.Opening
open DIRK12MidpointForward.Late DIRK12MidpointRealInterval DirectedRatBox
open DIRK12MidpointShape DIRK12MidpointGhost
open scoped Matrix BigOperators Polynomial

noncomputable def fittedPayload (x f : ℝ) (L : Fin 10 → Fin 10 → ℝ) :=
  openingPayload x (thirdPayload x (fourthPayload x (fifthPayload x f L)))

theorem assembled_is_five (x f : ℝ) :
    assembled x f=fiveFeed x f (assembled x f).live :=
  installed_is_five x f (groupedAmplitude x f)

theorem assembled_wiring (x f : ℝ) :
    assembled x f=realFeed x f (alpha x (yOf x)) (mu x (yOf x)) (nu x)
      (fittedPayload x f (assembled x f).live) :=
  (assembled_is_five x f).trans rfl

theorem nonghost_nonterminal_cases {Q : Fin 15 → Prop}
    (o : Q 0) (h : ∀ j : Fin 5, Q (visible (Physical.head j)))
    (p10 : Q 10) (p11 : Q 11) (p12 : Q 12) (p13 : Q 13)
    (i : Fin 15) (gi : ¬ ghostRow i) (ti : i≠terminal) : Q i := by
  revert gi ti
  refine stage_cases (P:=fun t => ¬ghostRow t → t≠terminal → Q t) ?_ ?_ ?_ i
  · exact fun _ _ => o
  · intro g ng _
    exact (ng (ghost_hidden g)).elim
  · intro t
    refine Fin.addCases (m:=5) (n:=5) (motive:=fun v =>
        ¬ghostRow (visible v) → visible v≠terminal → Q (visible v))
      (fun j _ _ => h j) (fun k => ?_) t
    fin_cases k
    · exact fun _ _ => p10
    · exact fun _ _ => p11
    · exact fun _ _ => p12
    · exact fun _ _ => p13
    · exact fun _ nt => (nt rfl).elim

section Main
variable (x f : ℝ)
local notation "F" => (assembled x f)
local notation "Areal" => (Feed.tableau (assembled x f))
local notation "Breal" => (Feed.b (assembled x f))
local notation "Cphys" => (nodes Areal)
local notation "W" => (DualSupport12.moment Areal Breal)
local notation "rho5base" => (6*(1/2:ℝ)^6*(eps x+(excess:ℝ)))

theorem assembled_ghost_zero (g : Fin 4) : Breal (DIRK12MidpointForward.hidden g)=0 := by
  change physicalWeight x f (DIRK12MidpointForward.hidden g)=0
  rw [physicalWeight,ite_eq_left (ghost_hidden g)]

theorem assembled_node_terminal : Cphys terminal=1 := by
  rw [(F).nodes_tableau]
  exact literal_terminal_clock x f 0 0 0 (fun _ _ => 0)

theorem assembled_mode1_profile (i : Fin 10) :
    (F).mode1 i=nu x*actualProfile Areal 1 (visible i) := by
  rw [actualProfile,(F).nodes_tableau,Feed.clocks_visible]
  change realClock x f i*nu x*leg6 (realClock x f i)=
    nu x*(realClock x f i*leg6 (realClock x f i))
  ring

private theorem head_zero_quintic :
    DualSupport12.forward Areal 5 (visible 0)=0 := by
  have h := (F).read_live 0 (by decide) (4:Fin 5)
  change DualSupport12.forward Areal 5 (visible 0)=_ at h
  rw [h]
  have e0 : (F).mode0 0=(1/2:ℝ) := by
    change realClock x f 0*(alpha x (yOf x)*leg5 (realClock x f 0)+
      mu x (yOf x)*leg6 (realClock x f 0)+gammaFrom (alpha x (yOf x))*leg7 (realClock x f 0))=_
    rw [realClock_first,mode_normalization,mul_one]
  have e1 : (F).mode1 0=0 := by
    change realClock x f 0*nu x*leg6 (realClock x f 0)=_
    rw [realClock_first,leg6_half,mul_zero]
  have ec : (F).cVisible 0=(1/2:ℝ) := realClock_first x f
  have ea : (F).a=(1/2:ℝ) := rfl
  have el : (F).live_action 0 5=0 := by
    unfold Feed.live_action
    apply Finset.sum_eq_zero
    intro i _
    have z : (F).live 0 i=0 := by
      change Physical.live (zeroHead x f) (exactData x f) (Physical.head 0) i=0
      rw [Physical.live_head]
      rfl
    simp [z]
  rw [e0,e1,ec,ea]
  change (6:ℝ)*((F).live_action 0 5+_+_)-_=_
  rw [el]
  norm_num

theorem early_weighted (w : V15 ℝ) (o : w 0=0)
    (h : ∀ j : Fin 5, w (visible (Physical.head j))=0)
    (i : Fin 15) (small : i.val < 10) : Breal i*w i=0 := by
  revert small
  refine stage_cases (P:=fun i => i.val<10 → Breal i*w i=0) ?_ ?_ ?_ i
  · intro _
    rw [o,mul_zero]
  · intro g _
    rw [assembled_ghost_zero,zero_mul]
  · intro j hj
    simp only [visible_val] at hj
    let k : Fin 5 := ⟨j.val,by omega⟩
    have eq : Physical.head k=j := Fin.ext rfl
    rw [←eq,h,mul_zero]

noncomputable def quinticScale : ℝ := rho5base*nu x

section Roots
variable (hx : Encloses xBox x) (hf : Encloses fBox f)
  (hx0 : realX x=0) (hf0 : realF x f=0)

include hx hf hx0 in
theorem paid_head_forward (j : Fin 5) (m : Fin 4) :
    DualSupport12.forward Areal (m.val+1) (visible (Physical.head j))=0 := by
  rw [assembled_is_five]
  let L := (F).live
  fin_cases j
  · exact first_live_primitive x f _ _ _ (fittedPayload x f L) m
  · exact row6_paid x f (thirdPayload x (fourthPayload x (fifthPayload x f L))) hx m
  · exact row7_paid x f (fourthPayload x (fifthPayload x f L)) hx hx0 m
  · exact row8_paid x f (fifthPayload x f L) hx hx0 m
  · exact row9_paid x f L hx hf m

include hx hf hx0 in
theorem quintic_head (j : Fin 5) :
    DualSupport12.forward Areal 5 (visible (Physical.head j))=
      quinticScale x*actualProfile Areal 1 (visible (Physical.head j)) := by
  have reduce (j : Fin 5) : quinticScale x*actualProfile Areal 1 (visible (Physical.head j)) =
      rho5base*(F).mode1 (Physical.head j) := by
    rw [assembled_mode1_profile]
    unfold quinticScale
    ring
  rw [reduce]
  let L := (F).live
  fin_cases j
  · change DualSupport12.forward Areal 5 (visible 0)=rho5base*(F).mode1 0
    rw [head_zero_quintic]
    have z : (F).mode1 0=0 := by
      change realClock x f 0*nu x*leg6 (realClock x f 0)=_
      rw [realClock_first,leg6_half,mul_zero]
    rw [z,mul_zero]
  · rw [assembled_is_five]
    let L' := thirdPayload x (fourthPayload x (fifthPayload x f L))
    have e := row6_actual x f L' hx (4:Fin 5)
    have b := (row6_modes x f L' hx).2
    change DualSupport12.forward (openingFeed x f L').tableau 5 (visible 1)=_ at e
    change DualSupport12.forward (openingFeed x f L').tableau 5 (visible 1)=
      rho5base*(openingFeed x f L').mode1 1
    rw [e,b]
    norm_num
    ring
  · rw [assembled_is_five]
    let L' := fourthPayload x (fifthPayload x f L)
    have e := row7_actual x f L' hx hx0 (4:Fin 5)
    have b := (row7_modes x f L' hx).2
    change DualSupport12.forward (threeFeed x f L').tableau 5 (visible 2)=_ at e
    change DualSupport12.forward (threeFeed x f L').tableau 5 (visible 2)=
      rho5base*(threeFeed x f L').mode1 2
    rw [e,b]
    norm_num
    ring
  · rw [assembled_is_five]
    let L' := fifthPayload x f L
    have e := row8_actual x f L' hx hx0 (4:Fin 5)
    have b := (row8_modes x f L').2
    change DualSupport12.forward (fourFeed x f L').tableau 5 (visible 3)=_ at e
    change DualSupport12.forward (fourFeed x f L').tableau 5 (visible 3)=
      rho5base*(fourFeed x f L').mode1 3
    rw [e,b]
    norm_num
    ring
  · rw [assembled_is_five]
    have e := row9_actual x f L hx hf (4:Fin 5)
    have b := (row9_modes x f L).2
    change DualSupport12.forward (fiveFeed x f L).tableau 5 (visible 4)=_ at e
    change DualSupport12.forward (fiveFeed x f L).tableau 5 (visible 4)=
      rho5base*(fiveFeed x f L).mode1 4
    rw [e,b]
    norm_num
    ring

include hx hf in
theorem assembled_late_profile (w : V15 ℝ)
    (early : ∀ i : Fin 15, i.val < 10 → Breal i*w i=0)
    (pair : w 11=w 13)
    (pay : ∀ k : Fin 3, row (W (k.val+1)) w=0) :
    w 10=0 ∧ w 11=0 ∧ w 12=0 ∧ w 13=0 := by
  have result := real_late_profile x f (alpha x (yOf x)) (mu x (yOf x)) (nu x)
    (fittedPayload x f (F).live) hx hf
  rw [←assembled_wiring x f] at result
  exact result w early pair pay

include hx hf hx0 hf0

theorem assembled_quad :
    ∀ p : ℝ[X], p.natDegree < 12 →
      DIRK12MidpointStar.quadr Areal Breal p=DIRK12MidpointRealInterval.integral p :=
  (scalar_and_star_with_physical_weights hx hf hx0 hf0 Areal (assembled_real_nodes x f)).1

theorem assembled_adjoint :
    mat (Matrix.transpose Areal) Breal=Breal*(1-(F).clocks) := by
  have e := real_adjoint x f (alpha x (yOf x)) (mu x (yOf x)) (nu x)
    (fittedPayload x f (F).live) hx hf hx0 hf0
  rw [←assembled_wiring x f] at e
  exact e

theorem primitive_paid_probes (m : Nat) (hm : m≤7) (k : Fin 3) :
    row (W (k.val+1)) (DualSupport12.forward Areal m)=0 :=
  paid_reverse_to_forward_moment (assembled_scalar x f hx hf hx0 hf0) (k.val+1) m
    (by have tk := k.isLt; omega) (reverse_low_silent x f hx hf hx0 hf0 k m hm)

theorem assembled_forward_small (m : Fin 4) (i : Fin 15)
    (hi : ¬ghostRow i) (ht : i≠terminal) :
    DualSupport12.forward Areal (m.val+1) i=0 := by
  let w := DualSupport12.forward Areal (m.val+1)
  have o : w 0=0 := (F).primitive_origin _
  have h : ∀ j : Fin 5, w (visible (Physical.head j))=0 :=
    fun j => paid_head_forward x f hx hf hx0 j m
  have ⟨p10,p11,p12,p13⟩ := assembled_late_profile x f hx hf w (early_weighted x f w o h)
    (actual_pair_forward x f hx hf (m.val+1) (by omega))
    (fun k => primitive_paid_probes x f hx hf hx0 hf0 (m.val+1) (by omega) k)
  exact nonghost_nonterminal_cases (Q:=fun i => w i=0) o h p10 p11 p12 p13 i hi ht

theorem assembled_forward_budget : (F).LiveBudget := by
  intro m i ih
  exact ((F).budget_at_iff i ih m).2
    (assembled_forward_small x f hx hf hx0 hf0 m (visible i) (non_ghost_visible i) ih)

theorem assembled_fw_primitive (m : Nat) (hm : m < 5) :
    DualSupport12.forward Areal m ∈ forwardBand ℝ (m+1) := by
  have bT : Breal terminal≠0 := (assembled_geom x f hx hf).bNZ 9
  apply (F).fw_primitive bT (assembled_ghost_zero x f) (assembled_adjoint x f hx hf hx0 hf0)
  · rw [←(F).nodes_tableau]
    exact assembled_scalar x f hx hf hx0 hf0
  · exact assembled_forward_budget x f hx hf hx0 hf0
  · exact hm

theorem actual_quintic_profile (i : Fin 15) (hi : ¬ghostRow i) (ht : i≠terminal) :
    DualSupport12.forward Areal 5 i=quinticScale x*actualProfile Areal 1 i := by
  let z := DualSupport12.forward Areal 5
  let v := quinticScale x • actualProfile Areal 1
  let w := z-v
  have o : w 0=0 := by
    have z0 : z 0=0 := (F).primitive_origin 5
    have v0 : v 0=0 := by
      simp only [v,actualProfile,Pi.smul_apply,smul_eq_mul,(F).nodes_tableau,
        Feed.clocks_origin,zero_mul,mul_zero]
    change z 0-v 0=0
    rw [z0,v0,sub_zero]
  have h (j : Fin 5) : w (visible (Physical.head j))=0 :=
    sub_eq_zero.mpr (quintic_head x f hx hf hx0 j)
  have pair : w 11=w 13 := by
    have l := actual_pair_forward x f hx hf 5 (by decide)
    have r := Physical.same_seed_clocks _ _ (assembled_geom x f hx hf)
    change Cphys 11=Cphys 13 at r
    change z 11-v 11=z 13-v 13
    change z 11=z 13 at l
    rw [l]
    simp [v,actualProfile,r]
  have pv (k : Fin 3) : row (W (k.val+1)) v=0 := by
    let j : Fin 7 := ⟨k.val+1,by omega⟩
    have e := profile_probe Areal Breal (assembled_quad x f hx hf hx0 hf0) 1 j
      (by dsimp [j]; omega) (by dsimp [j]; omega)
    have nz : j≠0 := by intro e; have q := congrArg Fin.val e; change k.val+1=0 at q; omega
    rw [ite_eq_right nz] at e
    change row (W (k.val+1)) (actualProfile Areal 1)=0 at e
    dsimp only [v]
    rw [map_smul,smul_eq_mul,e,mul_zero]
  have tests (k : Fin 3) : row (W (k.val+1)) w=0 := by
    change row (W (k.val+1)) (z-v)=0
    rw [map_sub,pv,sub_zero]
    exact primitive_paid_probes x f hx hf hx0 hf0 5 (by decide) k
  obtain ⟨p10,p11,p12,p13⟩ := assembled_late_profile x f hx hf w (early_weighted x f w o h) pair tests
  exact sub_eq_zero.mp (nonghost_nonterminal_cases (Q:=fun i => w i=0) o h p10 p11 p12 p13 i hi ht)

theorem actual_quintic_output : row Breal (DualSupport12.forward Areal 5)=0 := by
  have e := paid_reverse_to_forward_moment (assembled_scalar x f hx hf hx0 hf0)
    0 5 (by decide) (quiet:=by
      rw [reverse_grade1 x f hx hf hx0 hf0]
      simp)
  simpa using e

theorem actual_quintic_bridge (B : Nat → Submodule ℝ (V15 ℝ))
    (silentB : ∀ z∈B 5, ∀ k≤6, row z (Cphys^k)=0)
    (ghostB : ∀ z∈B 5, DualSupport12.zeroAt ghostRow z)
    (terminalB : ∀ z∈B 5, z terminal=0) :
    DualSupport12.forward Areal 5 ∈ DualSupport12.high Areal Breal B 5 := by
  apply actual_profile_bridge Areal Breal _ B ghostRow terminal (quinticScale x)
    (assembled_quad x f hx hf hx0 hf0) (assembled_node_terminal x f) silentB ?_
    ghostB terminalB (actual_quintic_profile x f hx hf hx0 hf0)
    (actual_quintic_output x f hx hf hx0 hf0)
  intro i h
  change physicalWeight x f i=0
  rw [physicalWeight,ite_eq_left h]

end Roots
end Main
end RKResearch.Certified.DIRK12MidpointReverse.Actual

#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.assembled_fw_primitive
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.actual_quintic_profile
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.actual_quintic_bridge
