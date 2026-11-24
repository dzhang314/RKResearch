module

public import RKCert.ReviewedNative.ForwardInvariantCap

@[expose] public section

/-! # Single forward head above a five-dimensional physical carrier -/
namespace RKResearch.Certified.Graded
open Module RKCert.OneEscape

section Quotient
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
/-- Any flag piece not contained in the terminal invariant core increases
its summed dimension at every subsequent clock step up to the horizon. -/
theorem terminal_quotient_growth (T:V→ₗ[K]V) (F:ℕ→Submodule K V) {m j:ℕ}
    (mono:Monotone F) (hstep:∀k,(F k).map T≤F (k+1))
    {U:Submodule K V} (hU:U≤F m) (hi:U.map T≤U)
    (largest:∀W:Submodule K V,W≤F m → W.map T≤W → W≤U)
    (hj:j≤m) (outside:¬F j≤U) :
    finrank K (F j ⊔ U : Submodule K V)+(m-j)≤finrank K (F m) := by
  let G (l:ℕ):Submodule K V:=F l ⊔ U
  have hmono:Monotone G:=fun _ _ le=>sup_le_sup_right (mono le) U
  have out (l:ℕ) (jl:j≤l) (lm:l≤m):¬(G l).map T≤G l := by
    intro inv
    exact outside ((mono jl).trans (le_sup_left.trans (largest _ (sup_le (mono lm) hU) inv)))
  have gain (r:ℕ) (hr:j+r≤m) : finrank K (G j)+r≤finrank K (G (j+r)) := by
    induction r with
    | zero=>simp
    | succ r ih=>
      have before:=ih (by omega)
      have step:G (j+r)<G (j+r+1):=lt_of_le_of_ne (hmono (by omega)) (fun eqn=>out (j+r) (by omega) (by omega) (by
        calc
          (G (j+r)).map T ≤ G (j+r+1) := by
            change ((F (j+r) ⊔ U : Submodule K V).map T)≤F (j+r+1) ⊔ U
            rw [Submodule.map_sup]
            exact sup_le ((hstep _).trans le_sup_left) (hi.trans le_sup_right)
          _ = G (j+r) := eqn.symm))
      have rank:=Submodule.finrank_lt_finrank_of_lt step
      change _≤finrank K (G (j+r+1))
      omega
  have g:=gain (m-j) (by omega)
  rw [show j+(m-j)=m by omega] at g
  rw [show G m=F m from sup_eq_left.mpr hU] at g
  exact g
end Quotient

variable {K : Type*} [Field K] [CharZero K] {s q : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {U : Submodule K (Fin s→K)}
set_option maxRecDepth 3500
set_option maxHeartbeats 1000000

structure FiveHiddenStaircase (A:Matrix (Fin s) (Fin s) K)
    (q:ℕ)(U:Submodule K ((Fin s→K)))(w:(Fin s→K)) : Prop where
  inside : U≤zeroSpace A 6
  headGrade : w∈zeroSpace A 5
  outside : w∉U
  midpoint : zeroSpace A q=chain (diag (nodes A)) U w (q-4)
  flags : ∀k,6≤k→k≤q→zeroSpace A k=chain (diag (nodes A)) U w (k-4)

theorem five_hidden_staircase (ha : ∀ i j,i≤j → A i j=0)
    (h8 : 8≤q) (sep : ∀ a, coeffEval A q a∈zeroSpace A q → a=0)(fm:finrank K (zeroSpace A q)=q+1)
    (fn:finrank K (zeroSpace A (q+1))≤q+3)
    (rank:finrank K U=5)(inc:U≤zeroSpace A q)(inv:U.map (diag (nodes A))≤U) :
    ∃w:(Fin s→K),FiveHiddenStaircase A q U w:=by
  have ps : PolySeparated A q := PolySeparated.of_coeff sep
  let F:=zeroSpace A
  let C:=diag (nodes A)
  let G(j:ℕ):Submodule K ((Fin s→K)):=F j⊔U
  have mono:Monotone F:=fun _ _ h=>zeroSpace_mono A h
  have step(j:ℕ):(F j).map C≤F (j+1):=Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A j)
  have maxim(W:Submodule K ((Fin s→K)))(hi:W≤F q)(hw:W.map C≤W):W≤U:=by
    have eq:U⊔W=U:=by
      apply (Submodule.eq_of_le_of_finrank_le le_sup_left ?_).symm
      apply (invariant_core_cap_of_rank ha h8 sep fm fn _ (sup_le inc hi) ?_).trans
      · omega
      · rw [Submodule.map_sup]
        exact sup_le (inv.trans le_sup_left) (hw.trans le_sup_right)
    exact le_sup_right.trans (le_of_eq eq)
  have hi(j:ℕ)(hj:1≤j)(jt:j≤q):finrank K (F j)≤j+1:=by
    have h:=zeroSpace_rank_interval_of_separation ha sep (j:=j) (d:=q-j) hj (by omega)
    rw [show j+(q-j)=q by omega,fm] at h
    change finrank K (F j)+(q-j)≤q+1 at h;omega
  have low:5≤finrank K (F 5):=grade_five_surplus ha (ps.mono (by omega))
  have no5:¬F 5≤U:=by
    intro fi
    have hef:F 5=U:=Submodule.eq_of_le_of_finrank_le fi (by omega)
    have e:=clock_invariant_outgoing ha (ps.mono (by omega : 5≤q)) hef.ge inv
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
  have next(j:ℕ):(G j⊔(G j).map C : Submodule K ((Fin s→K)))≤G (j+1):=
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
      exact clock_chain_next inv (by omega)
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
    · have grow:=clock_invariant_outgoing ha (ps.mono (by omega : 5≤q)) (U:=I) inf_le_left iInv
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
  exact ⟨w,completed,hw,wo,Fq,flag⟩

end RKResearch.Certified.Graded
