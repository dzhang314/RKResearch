module

public import RKCert.ReviewedNative.DIRK12MidpointForwardFlags
public import RKCert.ReviewedNative.DIRKOrderTwelveMidpointOpeningGhostCore
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

@[expose] public section

/-! Read any single physical nonterminal live row, with the exact
unpaid sixth ghost term left in the formula. -/
namespace RKResearch.Certified.DIRK12MidpointForward

open RKResearch Graded DIRK12MidpointGhost
open scoped BigOperators Matrix

variable {K : Type*} [Field K] [CharZero K]

namespace Feed

variable (P : Feed K)

def live_action (i : Fin 10) (j : Nat) : K :=
  ∑ s : Fin 10, (if i<s then 0 else P.live i s)*P.cVisible s^j

def live_budget_at (i : Fin 10) (m : Fin 4) : Prop :=
  ((m.val+2:Nat):K)*P.live_action i (m.val+1) + P.mode0 i*P.a^(m.val+1) +
    (((m.val+2:Nat):K)/((m.val+3:Nat):K))*P.mode1 i*P.a^(m.val+2) =
      P.cVisible i^(m.val+2)

private theorem tap_integral (k : Fin 6) :
    (∑ g : Fin 4, (tap g:K)*(clock g:K)^(k.val+1)) =
      1/((k.val+2:Nat):K) + if k.val=5 then (excess:K) else 0 := by
  have e := congrArg (fun q : Rat => (q:K)) (tap_moments_through_six k)
  by_cases h : k.val=5
  · simpa [add4,add_assoc,Fin.sum_univ_succ,momentSix,h,Rat.cast_div] using e
  · simpa [add4,add_assoc,Fin.sum_univ_succ,momentSix,h,Rat.cast_div] using e

theorem read_live (i : Fin 10) (hi : visible i≠terminal) (m : Fin 5) :
    DualSupport12.forward P.tableau (m.val+1) (visible i) =
      ((m.val+2:Nat):K)*
        (P.live_action i (m.val+1) +
          (P.mode0 i*P.a^(m.val+1))*(1/((m.val+2:Nat):K)) +
          (P.mode1 i*P.a^(m.val+2))*
            (1/((m.val+3:Nat):K)+if m.val=4 then (excess:K) else 0)) -
      P.cVisible i^(m.val+2) := by
  have step : m.val+1+1=m.val+2 := by omega
  have next : m.val+1+2=m.val+3 := by omega
  rw [DualSupport12.forward,P.nodes_tableau]
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.pow_apply]
  change ((m.val+1+1:Nat):K)*
      (∑ s, P.tableau (visible i) s*P.clocks s^(m.val+1)) -
      P.clocks (visible i)^(m.val+1+1) = _
  rw [step,sum_stages]
  simp only [clocks_origin,zero_pow (by omega : m.val+1≠0),mul_zero,zero_add,
    P.tableau_nonterminal_tap _ _ hi,P.tableau_nonterminal_live _ _ hi,clocks_visible]
  have gf (g : Fin 4) : P.ghostTap i g*P.clocks (hidden g)^(m.val+1) =
    (P.mode0 i*P.a^(m.val+1))*((tap g:K)*(clock g:K)^(m.val+1)) +
    (P.mode1 i*P.a^(m.val+2))*((tap g:K)*(clock g:K)^(m.val+2)) := by
    simp only [ghostTap,clocks_hidden,mul_pow,← step,pow_succ]
    ring
  simp_rw [gf]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
    tap_integral (K:=K) (⟨m.val,by omega⟩ : Fin 6),
    tap_integral (K:=K) (⟨m.val+1,by omega⟩ : Fin 6)]
  simp only [show m.val≠5 by omega,ite_false,add_zero,next,
    show (m.val+1=5) ↔ m.val=4 by omega,live_action]
  ring

theorem budget_at_iff (i : Fin 10) (hi : visible i≠terminal) (m : Fin 4) :
    P.live_budget_at i m ↔ DualSupport12.forward P.tableau (m.val+1) (visible i)=0 := by
  rw [P.read_live i hi (⟨m.val,by omega⟩ : Fin 5),live_budget_at]
  simp only [show m.val≠4 by omega,ite_false,add_zero]
  have nz : ((m.val+2:Nat):K)≠0 := Nat.cast_ne_zero.mpr (by omega)
  constructor <;> intro h
  · field_simp [nz] at h ⊢
    linear_combination h
  · field_simp [nz] at h ⊢
    linear_combination h

end Feed

end RKResearch.Certified.DIRK12MidpointForward

#print axioms RKResearch.Certified.DIRK12MidpointForward.Feed.read_live
#print axioms RKResearch.Certified.DIRK12MidpointForward.Feed.budget_at_iff
