module

public import RKCert.ReviewedNative.DIRK12MidpointReverseGuards
public import RKCert.ReviewedNative.DIRK12MidpointLegendreProbes
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

@[expose] public section

/-! A wired grouped extension keeps the verified five opening rows.
The actual ghost projection of each positive reverse read through
degree four vanishes by the existing paid scalar Legendre probes. -/
namespace RKResearch.Certified.DIRK12MidpointReverse.Actual

open RKResearch Graded DualSupport12
open DIRK12MidpointForward DIRK12MidpointForward.Opening
open DIRK12MidpointRealInterval DirectedRatBox DIRK12MidpointShape
open scoped Matrix BigOperators Polynomial

theorem installed_is_five (x f : ℝ) (h : Fin 6 → ℝ) :
    installed x f h=fiveFeed x f (installed x f h).live := by
  let P := fiveFeed x f (fun _ _=>0)
  let D := data x f h
  let L := Physical.live P D
  let rebuild : (Fin 10 → Fin 10 → ℝ) → Feed ℝ := fun taps => { P with live := taps }
  change rebuild L=rebuild (fiveFeed x f L).live
  apply congrArg rebuild
  funext i j
  refine Fin.addCases (m:=5) (n:=5) (motive:=fun i => L i j=(fiveFeed x f L).live i j)
    (fun k => ?_) (fun k => ?_) i
  · change L (Physical.head k) j=(fiveFeed x f L).live (Physical.head k) j
    rw [show L (Physical.head k) j=P.live (Physical.head k) j from Physical.live_head P D k j]
    fin_cases k
    · rfl
    · change P.live 1 j=(fiveFeed x f L).live 1 j
      by_cases e : j=0 <;> simp [P,fiveFeed,fourFeed,threeFeed,openingFeed,realFeed,
        openingPayload,thirdPayload,fourthPayload,fifthPayload,e]
    · change P.live 2 j=(fiveFeed x f L).live 2 j
      simp [P,fiveFeed,fourFeed,threeFeed,openingFeed,realFeed,openingPayload,
        thirdPayload,fourthPayload,fifthPayload]
    · change P.live 3 j=(fiveFeed x f L).live 3 j
      simp [P,fiveFeed,fourFeed,threeFeed,openingFeed,realFeed,openingPayload,
        thirdPayload,fourthPayload,fifthPayload]
    · change P.live 4 j=(fiveFeed x f L).live 4 j
      simp [P,fiveFeed,fourFeed,threeFeed,openingFeed,realFeed,openingPayload,
        thirdPayload,fourthPayload,fifthPayload]
  · have neq (a : Fin 10) (ha : a.val < 5) : (k.addNat 5 : Fin 10)≠a := by
      intro e
      have q := congrArg Fin.val e
      change k.val+5=a.val at q
      omega
    rw [Fin.natAdd_eq_addNat]
    simp only [fiveFeed,fourFeed,threeFeed,openingFeed,realFeed,openingPayload,
      thirdPayload,fourthPayload,fifthPayload,
      ite_eq_right (neq 0 (by decide)),ite_eq_right (neq 1 (by decide)),
      ite_eq_right (neq 2 (by decide)),ite_eq_right (neq 3 (by decide)),
      ite_eq_right (neq 4 (by decide))]

section GhostRead

variable (x f alpha mu nu : ℝ) (L : Fin 10 → Fin 10 → ℝ)
local notation "Fphys" => (realFeed x f alpha mu nu L)
local notation "Aphys" => (Feed.tableau (realFeed x f alpha mu nu L))

private theorem g_tap_combo (g : Fin 4) (i : Fin 10)
    (nt : visible i≠terminal) :
    Aphys (visible i) (DIRK12MidpointForward.hidden g)=
      (DIRK12MidpointGhost.tap g:ℝ)*
        (∑ d : Fin 3, ((![alpha,mu+nu*(Fphys).clocks (DIRK12MidpointForward.hidden g),
                      gammaFrom alpha] : Fin 3 → ℝ) d • actualProfile Aphys d) (visible i)) := by
  have hc : nodes Aphys (visible i)=realClock x f i := by
    rw [(Fphys).nodes_tableau,Feed.clocks_visible]
    rfl
  rw [(Fphys).tableau_nonterminal_tap i g nt,Feed.ghostTap,Fin.sum_univ_three]
  congr 1
  simp only [actualProfile,hc,Pi.smul_apply,smul_eq_mul]
  norm_num [leg,realFeed]
  ring

theorem real_reverse_ghost_read (hx : Encloses xBox x) (hf : Encloses fBox f)
    (hx0 : realX x=0) (hf0 : realF x f=0) (g : Fin 4) (m : Fin 4) :
    mat (Matrix.transpose Aphys) (DualSupport12.moment Aphys (Fphys).b (m.val+1))
      (DIRK12MidpointForward.hidden g)=0 := by
  let Q : Fin 3 → ℝ := ![alpha,mu+nu*(Fphys).clocks (DIRK12MidpointForward.hidden g),gammaFrom alpha]
  let V := ∑ d : Fin 3, Q d • actualProfile Aphys d
  let W := DualSupport12.moment Aphys (Fphys).b (m.val+1)
  let ell : ℝ := DIRK12MidpointGhost.tap g
  have q := (scalar_and_star_with_physical_weights hx hf hx0 hf0 Aphys
    (real_nodes x f alpha mu nu L)).1
  have pay : row W V=0 := probe_combo_positive Aphys (Fphys).b q Q m
  have entry (i : Fin 15) :
      Aphys i (DIRK12MidpointForward.hidden g)*W i=ell*(W i*V i) := by
    apply stage_cases (P:=fun i => Aphys i (DIRK12MidpointForward.hidden g)*W i=ell*(W i*V i))
      ?_ ?_ ?_ i
    · have v0 : V 0=0 := by
        simp [V,actualProfile,(Fphys).nodes_tableau]
      rw [(Fphys).tableau_origin,zero_mul,v0,mul_zero,mul_zero]
    · intro j
      have w0 : W (DIRK12MidpointForward.hidden j)=0 := by
        change (Fphys).b (DIRK12MidpointForward.hidden j)*
          (reflected Aphys (DIRK12MidpointForward.hidden j))^(m.val+1)=0
        rw [real_ghost_weights x f alpha mu nu L,zero_mul]
      rw [w0,mul_zero,zero_mul,mul_zero]
    · intro j
      by_cases nt : visible j=terminal
      · rw [nt]
        have w0 : W terminal=0 := by
          change (Fphys).b terminal * (1-nodes Aphys terminal)^(m.val+1)=0
          rw [(Fphys).nodes_tableau,literal_terminal_clock x f alpha mu nu L,sub_self,
            zero_pow (by omega : m.val+1≠0),mul_zero]
        rw [w0,mul_zero,zero_mul,mul_zero]
      · rw [g_tap_combo x f alpha mu nu L g j nt]
        change ell*(∑ d : Fin 3, (Q d • actualProfile Aphys d) (visible j))*W (visible j)=_
        simp only [V,Finset.sum_apply]
        ring
  change (∑ i, Aphys i (DIRK12MidpointForward.hidden g)*W i)=0
  simp_rw [entry]
  rw [← Finset.mul_sum]
  change ell*row W V=0
  rw [pay,mul_zero]

end GhostRead
end RKResearch.Certified.DIRK12MidpointReverse.Actual

#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.installed_is_five
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.real_reverse_ghost_read
