module

public import RKCert.ReviewedNative.DIRK12MidpointPaidBridgeProfiles
public import RKCert.ReviewedNative.DIRK12MidpointOpeningRead
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

@[expose] public section

/-! The literal images of the three ghost generators have the required
degree-six live profile, independently of open later live-to-live entries. -/
namespace RKResearch.Certified.DIRK12MidpointForward

open RKResearch Graded DualSupport12VectorReplay DIRK12MidpointGhost
open DIRK12MidpointShape DIRK12MidpointRealInterval DirectedRatBox
open scoped Matrix BigOperators Polynomial

private theorem tapLift (k : Fin 3) :
    (∑ g : Fin 4, (tap g:ℝ)*(lift k.val g:ℝ))=0 := by
  have h := congrArg (fun r:Rat => (r:ℝ)) (tap_annihilates k)
  simpa [add4,add_assoc,Fin.sum_univ_succ] using h

private theorem tapNextLift (k : Fin 3) :
    (∑ g : Fin 4, (tap g:ℝ)*(lift (k.val+1) g:ℝ))=
      if k=2 then -1/47520 else 0 := by
  have a : (∑ g : Fin 4, (tap g:ℝ)*(lift 3 g:ℝ))=(-1:ℝ)/47520 := by
    have h := congrArg (fun r:Rat => (r:ℝ)) cubic_third_lift_tap
    simpa [add4,add_assoc,Fin.sum_univ_succ,Rat.cast_div] using h
  fin_cases k
  · simpa using tapLift 1
  · simpa using tapLift 2
  · simpa using a

theorem Feed.third_lift_profile (P : Feed ℝ) (i : Fin 10) (hi : visible i≠terminal) (k : Fin 3) :
    mat P.tableau (gen k.val) (visible i)=
      P.mode1 i*P.a*(if k=2 then -1/47520 else 0) := by
  change (∑ j : Fin 15, P.tableau (visible i) j*gen k.val j)=_
  rw [sum_stages]
  simp only [gen_origin,gen_visible,gen_hidden,mul_zero,Finset.sum_const_zero,zero_add,add_zero,
    P.tableau_nonterminal_tap _ _ hi,Feed.ghostTap,Feed.clocks_hidden]
  have e (g : Fin 4) :
      (tap g:ℝ)*(P.mode0 i+P.mode1 i*(P.a*(clock g:ℝ)))*(lift k.val g:ℝ)=
        P.mode0 i*((tap g:ℝ)*(lift k.val g:ℝ))+
        (P.mode1 i*P.a)*((tap g:ℝ)*(lift (k.val+1) g:ℝ)) := by
    simp only [lift,Rat.cast_mul,Rat.cast_pow,pow_succ]
    ring
  simp_rw [e]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,tapLift,tapNextLift,mul_zero,zero_add]

section Actual

variable (x f alpha mu nu : ℝ) (L : Fin 10 → Fin 10 → ℝ)
local notation "thisFeed" => realFeed x f alpha mu nu L

theorem real_AG5_bridge
    (hx : Encloses xBox x) (hf : Encloses fBox f)
    (hx0 : realX x=0) (hf0 : realF x f=0)
    (B : Nat → Submodule ℝ (Fin 15 → ℝ))
    (silentB : ∀ z∈B 5, ∀ k≤6, row z ((nodes (thisFeed).tableau)^k)=0)
    (ghostB : ∀ z∈B 5, DualSupport12.zeroAt ghost z)
    (terminalB : ∀ z∈B 5, z terminal=0) :
    ∀ w ∈ forwardBand ℝ 5, mat (thisFeed).tableau w ∈
      DualSupport12.high (thisFeed).tableau (thisFeed).b B 5 := by
  have q := (scalar_and_star_with_physical_weights hx hf hx0 hf0 (thisFeed).tableau
    (real_nodes x f alpha mu nu L)).1
  have bGhost : DualSupport12.zeroAt ghost (thisFeed).b := by
    intro i e
    change physicalWeight x f i=0
    rw [physicalWeight,ite_eq_left (show ghostRow i from e)]
  apply span_by_linear (gen (K:=ℝ)) 5 (M:=mat (thisFeed).tableau)
  intro k
  have k3 : k.val<3 := k.isLt
  let g : Fin 3 := ⟨k.val,k3⟩
  let rho : ℝ := nu*(1/2)*(if g=2 then -1/47520 else 0)
  apply actual_profile_bridge (thisFeed).tableau (thisFeed).b _ B ghost terminal rho q
  · rw [(thisFeed).nodes_tableau,literal_terminal_clock x f alpha mu nu L]
  · exact silentB
  · exact bGhost
  · exact ghostB
  · exact terminalB
  · apply stage_cases
    · intro _ _
      have Arow : mat (thisFeed).tableau (gen k.val) 0=0 := by
        change (∑ i : Fin 15, (thisFeed).tableau 0 i*gen k.val i)=0
        simp [(thisFeed).tableau_origin]
      rw [Arow,actualProfile,(thisFeed).nodes_tableau,(thisFeed).clocks_origin]
      ring
    · intro h e
      exact (e (ghost_hidden h)).elim
    · intro i _ ht
      have hm : (thisFeed).mode1 i=nu*actualProfile (thisFeed).tableau 1 (visible i) := by
        rw [actualProfile,(thisFeed).nodes_tableau]
        change realClock x f i*nu*leg6 (realClock x f i)=_
        rw [(thisFeed).clocks_visible]
        simp only [leg,show (1:Fin 3)≠0 by decide,ite_false,ite_true]
        change realClock x f i*nu*leg6 (realClock x f i)=
          nu*(realClock x f i*leg6 (realClock x f i))
        ring
      rw [(thisFeed).third_lift_profile i ht g,hm]
      change _*(1/2:ℝ)*(if g=2 then -1/47520 else 0)=_
      dsimp [rho]
      ring
  · have adj := real_adjoint x f alpha mu nu L hx hf hx0 hf0
    have dual :
        row (thisFeed).b (mat (thisFeed).tableau (gen k.val)) =
          row (mat (thisFeed).tableau.transpose (thisFeed).b) (gen k.val) := by
      rw [row_apply,row_apply,mat_apply,mat_apply,
        dotProduct_comm ((thisFeed).tableau.transpose *ᵥ (thisFeed).b),
        Matrix.dotProduct_transpose_mulVec]
    rw [dual,adj,row_apply,dotProduct,sum_stages]
    simp only [Pi.mul_apply,gen_origin,gen_visible,mul_zero,Finset.sum_const_zero,add_zero,
      real_ghost_weights x f alpha mu nu L,zero_mul]

end Actual
end RKResearch.Certified.DIRK12MidpointForward

#print axioms RKResearch.Certified.DIRK12MidpointForward.Feed.third_lift_profile
#print axioms RKResearch.Certified.DIRK12MidpointForward.real_AG5_bridge
