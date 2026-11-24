module
public import RKCert.ERKEvenInvariantCap
public import RKCert.ERKOddBalancedRanks
public import RKCert.DirkEvenCore

@[expose] public section
/-! # Five hidden dimensions pay a true one-head forward staircase -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint Module
variable {K:Type*} [Field K] [CharZero K] {s p q:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)}

structure FiveHiddenStaircase (A:Fin (s+1)→Fin (s+1)→K)
    (q:ℕ)(U:Submodule K (Vec K (s+1)))(w:Vec K (s+1)) : Prop where
  inside : U≤zeroSpace A 6
  headGrade : w∈zeroSpace A 5
  outside : w∉U
  midpoint : zeroSpace A q=chain (diag (nodes A)) U w (q-4)
  flags : ∀k,6≤k→k≤q→zeroSpace A k=chain (diag (nodes A)) U w (k-4)
  top : finrank K (zeroSpace A (q+1))≤q+2→
    zeroSpace A (q+1)=chain (diag (nodes A)) U w (q-3)

set_option maxHeartbeats 2800000 in
theorem five_hidden_staircase (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b p)
    (h8:8≤q)(pay:q+1≤p)(sep:Separated A q)(fm:finrank K (zeroSpace A q)=q+1)
    (fn:finrank K (zeroSpace A (q+1))≤q+3)
    (rank:finrank K U=5)(inc:U≤zeroSpace A q)(inv:U.map (diag (nodes A))≤U) :
    ∃w:Vec K (s+1),FiveHiddenStaircase A q U w:=by
  let F:=zeroSpace A
  let C:=diag (nodes A)
  let G(j:ℕ):Submodule K (Vec K (s+1)):=F j⊔U
  have mono:Monotone F:=fun _ _ h=>zeroSpace_mono A h
  have step(j:ℕ):(F j).map C≤F (j+1):=Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A j)
  have maxim(W:Submodule K (Vec K (s+1)))(hi:W≤F q)(hw:W.map C≤W):W≤U:=by
    have eq:U⊔W=U:=by
      apply (Submodule.eq_of_le_of_finrank_le le_sup_left ?_).symm
      apply (invariant_core_cap_of_rank ha ho h8 pay sep fm fn _ (sup_le inc hi) ?_).trans
      · omega
      · rw [Submodule.map_sup]
        exact sup_le (inv.trans le_sup_left) (hw.trans le_sup_right)
    exact le_sup_right.trans (le_of_eq eq)
  have hi(j:ℕ)(hj:1≤j)(jt:j≤q):finrank K (F j)≤j+1:=by
    have h:=strict_rank_interval ha sep j (q-j) hj (by omega)
    rw [show j+(q-j)=q by omega,fm] at h
    change finrank K (F j)+(q-j)≤q+1 at h;omega
  have low:5≤finrank K (F 5):=grade_five_surplus ha (sep.mono (by omega))
  have no5:¬F 5≤U:=by
    intro fi
    have hef:F 5=U:=Submodule.eq_of_le_of_finrank_le fi (by omega)
    have e:=forward_invariant_hermite_rank ha ho (j:=5) (by omega) U hef.ge
      (fun _ h=>inv (Submodule.mem_map_of_mem h))
    have d:=hi 6 (by decide) (by omega)
    change finrank K U+3≤finrank K (F 6) at e;omega
  obtain ⟨w,hw,wo⟩:=Set.not_subset.mp no5
  have ng(j:ℕ)(a:5≤j)(g:j≤q):¬(G j).map C≤G j:=by
    intro gg
    exact no5 ((mono a).trans (le_sup_left.trans (maxim _ (sup_le (mono g) inc) gg)))
  have compat(j:ℕ):(G j).map C≤G (j+1):=by
    change (F j⊔U).map C≤F (j+1)⊔U
    rw [Submodule.map_sup]
    exact sup_le ((step _).trans le_sup_left) (inv.trans le_sup_right)
  have next(j:ℕ):(G j⊔(G j).map C : Submodule K (Vec K (s+1)))≤G (j+1):=
    sup_le (sup_le_sup_right (mono (by omega)) U) (compat j)
  have more(j:ℕ)(a:5≤j)(g:j≤q):G j<G j⊔(G j).map C:=
    lt_of_le_of_ne le_sup_left (fun e=>ng j a g (le_sup_right.trans (le_of_eq e.symm)))
  have base:G 5=U⊔K∙w:=by
    symm
    apply Submodule.eq_of_le_of_finrank_le
    · exact sup_le le_sup_right ((Submodule.span_singleton_le_iff_mem ..).mpr
        ((show F 5≤G 5 from le_sup_left) hw))
    · rw [Submodule.finrank_sup_span_singleton wo,rank]
      have c:=terminal_quotient_growth C F mono step inc inv maxim (show 5≤q by omega) no5
      change finrank K (G 5)+(q-5)≤finrank K (F q) at c
      change finrank K (F q)=q+1 at fm
      omega
  have five:finrank K (G 5)=6:=by rw [base,Submodule.finrank_sup_span_singleton wo,rank]
  have floor(k:ℕ)(g:5+k≤q):6+k≤finrank K (G (5+k)):=by
    induction k with
    | zero=>simpa only [Nat.add_zero,five] using (le_rfl:6≤6)
    | succ k ih=>
      have f:=ih (by omega)
      have b:=Submodule.finrank_lt_finrank_of_lt ((more (5+k) (by omega) (by omega)).trans_le (next _))
      change finrank K (G (5+k))<finrank K (G (5+(k+1))) at b
      omega
  have gr(j:ℕ)(a:5≤j)(c:j≤q):finrank K (G j)=j+1:=by
    have r:=terminal_quotient_growth C F mono step inc inv maxim c
      (fun h=>no5 ((mono a).trans h))
    change finrank K (G j)+(q-j)≤finrank K (F q) at r
    change finrank K (F q)=q+1 at fm
    have l:=floor (j-5) (by omega)
    rw [show 5+(j-5)=j by omega] at l
    omega
  have bands(k:ℕ)(g:5+k≤q):G (5+k)=chain C U w (1+k):=by
    induction k with
    | zero=>simpa [chain] using base
    | succ k ih=>
      have eq:G (5+k+1)=G (5+k)⊔(G (5+k)).map C:=by
        symm
        apply Submodule.eq_of_le_of_finrank_le (next (5+k))
        have m:=Submodule.finrank_lt_finrank_of_lt (more (5+k) (by omega) (by omega))
        rw [gr (5+k) (by omega) (by omega)] at m
        rw [gr (5+k+1) (by omega) (by omega)]
        omega
      change G (5+k+1)=chain C U w (1+k+1)
      rw [eq,ih (by omega)]
      exact chain_sup_map inv (by omega)
  let I:=F 5⊓U
  have dimI:4≤finrank K I:=by
    have dim:=Submodule.finrank_sup_add_finrank_inf_eq (F 5) U
    change finrank K (G 5)+finrank K I=finrank K (F 5)+finrank K U at dim
    rw [five,rank] at dim;omega
  have completed:U≤F 6:=by
    by_cases high:5≤finrank K I
    · have e:I=U:=Submodule.eq_of_le_of_finrank_le inf_le_right (by omega)
      exact (le_of_eq e.symm).trans (inf_le_left.trans (mono (by decide)))
    by_cases iInv:I.map C≤I
    · have grow:=forward_invariant_hermite_rank ha ho (j:=5) (by omega) I inf_le_left
        (fun _ h=>iInv (Submodule.mem_map_of_mem h))
      have cc:finrank K (G 6)=7:=gr 6 (by decide) (by omega)
      change finrank K I+3≤finrank K (F 6) at grow
      have eq:F 6=G 6:=Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
      exact le_sup_right.trans eq.ge
    · let J:=I⊔I.map C
      have grow:finrank K I<finrank K J:=Submodule.finrank_lt_finrank_of_lt
        (lt_of_le_of_ne le_sup_left (fun e=>iInv (le_sup_right.trans (le_of_eq e.symm))))
      have hi:J≤U:=sup_le inf_le_right ((Submodule.map_mono inf_le_right).trans inv)
      have eq:J=U:=Submodule.eq_of_le_of_finrank_le hi (by omega)
      rw [←eq]
      exact sup_le (show I≤F 6 from inf_le_left.trans (mono (by decide:5≤6)))
        ((Submodule.map_mono (show I≤F 5 from inf_le_left)).trans (step 5))
  have flag(k:ℕ)(kl:6≤k)(kh:k≤q):F k=chain C U w (k-4):=by
    have e:=bands (k-5) (by omega)
    rw [show 5+(k-5)=k by omega,show 1+(k-5)=k-4 by omega,
      show G k=F k from sup_eq_left.mpr (completed.trans (mono kl))] at e
    exact e
  have Fq:=flag q (by omega) le_rfl
  refine ⟨w,completed,hw,wo,Fq,flag,?_⟩
  intro cap
  have non:¬(F q).map C≤F q:=by
    intro h
    have e:=forward_invariant_hermite_rank ha ho (j:=q) pay (F q) le_rfl
      (fun _ v=>h (Submodule.mem_map_of_mem v))
    change finrank K (F q)+(q+1)/2≤finrank K (F (q+1)) at e
    have r:finrank K (F q)=q+1:=fm
    change finrank K (F (q+1))≤q+2 at cap
    omega
  have one:finrank K (F (q+1))≤finrank K (F q)+1:=by rw [show finrank K (F q)=q+1 from fm];omega
  calc
    F (q+1)=F q⊔(F q).map C:=ordinary_step one non
    _=chain C U w (q-4+1):=by rw [Fq,chain_sup_map inv (by omega)]
    _=chain C U w (q-3):=by rw [show q-4+1=q-3 by omega]
end RKCert.Paired.FiniteMidpoint
