module
public import RKCert.ERKEvenHiddenCompletion
public import RKCert.ERKEvenBalancedHorizon

@[expose] public section
/-! # Native rank saturation at the first odd boundary above the field floor
The new physical width is 3q+2, not the field obstruction's smaller width.
An actual terminal coordinate is paid separately exactly when the first
adjoint seed vanishes. -/
namespace RKCert.Paired.FiniteMidpoint
open Module Polynomial RKCert.Paired.OrderTwelve RKCert.Paired.ReverseHull
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {s q p:ℕ}

theorem odd_rank_floor_from_eight {A:Fin s→Fin s→K} {b:Vec K s}
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b (2*q+1))(h8:8≤q):3*q+2≤s:=by
  have sep:Separated A q:=explicit_separated ha ho (by omega) (by
    have h:=explicit_order_le_stages ha ho;omega)
  have eight:=grade_eight_surplus_ordered ha ho (by omega)
  have grow:=strict_rank_interval ha sep 8 (q-8) (by decide) (by omega)
  rw [show 8+(q-8)=q by omega] at grow
  have e:=tree_rank_eq ho sep (by omega)
  have h:=backward_endpoint_count ha ho q (q-1) le_rfl (by omega)
  omega

variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
noncomputable section

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem anchored_band_next_separated (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b p)
    (sep:Separated A q) (pay:2*q+1≤p) (q1:1≤q) :
    ∀a:Fin (q+1)→K,polyEval A q a∈zeroSpace A (q+1)→a=0:=by
  intro a h
  apply (separated_iff_coeff A q).mp sep
  refine ERKEvenHidden.pure_of_anchored_zero_moments ha ho (by omega) (by omega)
    (polyEval_mem_treeSpace _ _ _) (origin_zeroSpace A ha _ h) ?_
  intro k hk
  exact probe_zeroSpace ho (by omega) h

/-- The arbitrary original array at the balanced odd count: the same one
dimension in the reverse budget is attributed to the real terminal or to
the linear reverse seed, never counted twice. -/
structure OddBalanced (A:Fin (s+1)→Fin (s+1)→K) (b:Vec K (s+1)) (q:ℕ) : Prop where
  separated : Separated A q
  lastLive : b (Fin.last s)≠0
  forwardMid : finrank K (zeroSpace A q)=q+1
  forwardCap : ∀j,1≤j→j≤q→finrank K (zeroSpace A j)≤j+1
  forwardLow : ∀j,5≤j→j≤q→j≤finrank K (zeroSpace A j)
  treeMid : finrank K (treeSpace A q)=2*q+2
  treePrev : 2*q-1≤finrank K (treeSpace A (q-1))
  nextCap : finrank K (zeroSpace A (q+1)) + finrank K (back A b 0)≤q+3
  lastReflect : backSeed1 A b=0→mirror A (Fin.last s)=0
  terminalOut : backSeed1 A b=0→terminal (K:=K) s∉treeSpace A q
  zeroCover : backSeed1 A b=0→
    back A b (q-1)=annih (treeSpace A q)⊓LinearMap.ker (LinearMap.proj (Fin.last s))
  nonzeroCover : backSeed1 A b≠0→back A b (q-1)=annih (treeSpace A q)
  flags : ∀n≤q-1,finrank K (back A b n)=n+finrank K (back A b 0) ∧
    back A b n=primitiveBack A b n

set_option maxHeartbeats 2100000 in
theorem balanced_odd_ranks (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b (2*q+1))
    (h8:8≤q)(size:s+1=3*q+2):OddBalanced A b q:=by
  have sep:Separated A q:=explicit_separated ha ho (by omega) (by omega)
  have live:b (Fin.last s)≠0:=by
    intro z
    have h:=odd_rank_floor_from_eight (trim_strict ha) (order_trim ha ho z) h8
    omega
  have f8:=grade_eight_surplus_ordered ha ho (by omega)
  have g8:=strict_rank_interval ha sep 8 (q-8) (by decide) (by omega)
  rw [show 8+(q-8)=q by omega] at g8
  have prev:=tree_rank_eq ho (sep.mono (show q-1≤q by omega)) (by omega)
  have mid:=tree_rank_eq ho sep (by omega)
  have ec:=backward_endpoint_count ha ho q (q-1) le_rfl (by omega)
  have fQ:finrank K (zeroSpace A q)=q+1:=by omega
  have eQ:finrank K (treeSpace A q)=2*q+2:=by omega
  have lowFive:=grade_five_surplus ha (sep.mono (show 5≤q by omega))
  have lower(j:ℕ)(a:5≤j)(c:j≤q):j≤finrank K (zeroSpace A j):=by
    have g:=strict_rank_interval ha sep 5 (j-5) (by decide) (by omega)
    rw [show 5+(j-5)=j by omega] at g
    omega
  have upper(j:ℕ)(a:1≤j)(c:j≤q):finrank K (zeroSpace A j)≤j+1:=by
    have g:=strict_rank_interval ha sep j (q-j) a (by omega)
    rw [show j+(q-j)=q by omega,fQ] at g
    omega
  have none : ∀i,Fin.last s < i → b i=0:=fun _ e=>False.elim ((not_lt_of_ge (Fin.le_last _)) e)
  have y(z:backSeed1 A b=0):mirror A (Fin.last s)=0:=last_mirror_zero ha live none z
  have col(i:Fin (s+1)):A i (Fin.last s)=0:=ha _ _ (Fin.le_last i)
  have out(z:backSeed1 A b=0):terminal (K:=K) s∉treeSpace A q:=
    terminal_single_not_mem ha ho le_rfl _ live ((sub_eq_zero.mp (y z)).symm)
  have add := poly_band_rank_add (anchored_band_next_separated ha ho sep (by omega) (by omega))
  have next_le:polyBand A q⊔zeroSpace A (q+1)≤treeSpace A (q+1):=
    sup_le (polyBand_le A (by omega)) (zeroSpace_le_treeSpace A _)
  have nr:=Submodule.finrank_mono next_le
  rw [add] at nr
  have countNext:=backward_count ha ho (q+1) (q-2) (by omega)
  have cap:finrank K (zeroSpace A (q+1))+finrank K (back A b 0)≤q+3:=by omega
  have lim:finrank K (primitiveBack A b (q-1))≤q-1+finrank K (back A b 0):=by
    by_cases z:backSeed1 A b=0
    · have lim:=annihilating_terminal_count (terminal s) (out z)
        (primitiveBack_annih ho q (q-1) (by omega)) (fun w hw=>by rw [row_terminal];exact primitiveBack_terminal _ (y z) col z _ hw)
      rw [eQ] at lim
      omega
    · have br:finrank K (back A b 0)=1:=finrank_span_singleton z
      have h:=finrank_annih_le (primitiveBack_annih ho q (q-1) (by omega))
      rw [eQ] at h
      omega
  have flags(n:ℕ)(low:n≤q-1):finrank K (back A b n)=n+finrank K (back A b 0) ∧
      back A b n=primitiveBack A b n:=by
    have g:=primitiveBack_interval ha ho n (q-1-n) (by omega)
    rw [show n+(q-1-n)=q-1 by omega] at g
    have flo:=back_finrank ha ho n (by omega)
    have inc:=back_le_primitiveBack (A:=A) (b:=b) n
    have nn:=Submodule.finrank_mono inc
    exact ⟨by omega,Submodule.eq_of_le_of_finrank_le inc (by omega)⟩
  refine ⟨sep,live,fQ,upper,lower,eQ,by have h:=lower (q-1) (by omega) (by omega);omega,cap,y,out,?_,?_,flags⟩
  · intro z
    let V:=annih (treeSpace A q)⊓LinearMap.ker (LinearMap.proj (Fin.last s))
    have inc:back A b (q-1)≤V:=le_inf (back_annih ho q (q-1) (by omega))
      (fun w hw=>back_vanish ha live none z _ hw _ le_rfl)
    have rank:= (flags (q-1) le_rfl).1
    have Z:finrank K (back A b 0)=0:=by change finrank K (K∙backSeed1 A b)=0;rw [z,Submodule.span_singleton_eq_bot.mpr rfl,finrank_bot]
    have note:=annihilating_terminal_count (terminal s) (out z) (show V≤annih _ from inf_le_left)
      (fun w hw=>by rw [row_terminal];exact hw.2)
    rw [Z,add_zero] at rank
    -- Rewrite only the numerical count, retaining the original annihilator.
    rw [eQ] at note
    change back A b (q-1)=V
    exact Submodule.eq_of_le_of_finrank_le inc (by omega)
  · intro z
    have rank:finrank K (back A b 0)=1:=finrank_span_singleton z
    have r:=(flags (q-1) le_rfl).1
    have bill:=finrank_annih_eq (treeSpace A q)
    rw [eQ] at bill
    exact Submodule.eq_of_le_of_finrank_le (back_annih ho q (q-1) (by omega)) (by omega)
end
end RKCert.Paired.FiniteMidpoint
