module

public import RKCert.ReviewedNative.ForwardInvariantCap

@[expose] public section

/-! # A four-dimensional hidden core is incompatible with refunded
ordinary profiles at grades five and six. The two visibility hypotheses
are charged prerequisites, not identifications of other tableaux. -/
namespace RKResearch.Certified.Graded
open Module RKCert.OneEscape
variable {K : Type*} [Field K] [CharZero K] {s q : ℕ}
variable {A : Matrix (Fin s) (Fin s) K}
set_option maxRecDepth 3500
set_option maxHeartbeats 1100000

theorem four_hidden_rank_dispatch (ha : ∀ i j,i≤j → A i j=0)
    (q8 : 8≤q) (sep : ∀ a, coeffEval A q a∈zeroSpace A q → a=0)
    (fmid:finrank K (zeroSpace A q)=q+1) (cap:finrank K (zeroSpace A (q+1))≤q+3)
    (H:Submodule K ((Fin s→K))) (hH:H≤zeroSpace A q) (dimH:finrank K H=4)
    (invH:H.map (diag (nodes A))≤H) (visible:Fin s→Prop)
    (blind:∀v∈H,∀i,visible i→v i=0)
    (detect:∀v∈zeroSpace A q,(∀i,visible i→v i=0)→v∈H)
    (oneSite:∀v∈zeroSpace A 6,(∃a:K,∀i,visible i→nodes A i≠a→v i=0)→v∈H)
    (drop:∀ j, j=5∨j=6 → ∀ w:(Fin s→K),
      (∀ k<j-3,(diag (nodes A)^k) w∈zeroSpace A j⊔H) → w∈H) :
    False := by
  have ps : PolySeparated A q := PolySeparated.of_coeff sep
  let C:=diag (nodes A)
  let F:=zeroSpace A
  obtain ⟨k,_,plat⟩:=exists_plateau C (F q)
  let U:=core C (F q) k
  have Ui:U≤F q:=fun _ hv=>by simpa only [pow_zero,one_apply_eq_self] using
    (mem_core.mp hv 0 (Nat.zero_le _))
  have Ul:U.map C≤U:=invariant_of_plateau plat
  have maxU (V:Submodule K ((Fin s→K))) (hv:V.map C≤V) (hq:V≤F q) : V≤U:=
    invariant_le_core hq hv k
  have HU:H≤U:=maxU H invH hH
  have uc:=invariant_core_cap_of_rank ha q8 sep fmid cap U Ui Ul
  have ulo:=Submodule.finrank_mono HU
  rw [dimH] at ulo
  have f5:5≤finrank K (F 5):=grade_five_surplus ha (ps.mono (by omega))
  have up (j:ℕ) (lo:1≤j) (hi:j≤q) : finrank K (F j)≤j+1 := by
    have G:=zeroSpace_rank_interval_of_separation ha sep (j:=j) (d:=q-j) lo (by omega)
    rw [show j+(q-j)=q by omega,fmid] at G
    change finrank K (zeroSpace A j)≤j+1
    omega
  have non5 : ¬F 5≤U := by
    intro cf
    have eq:=Submodule.eq_of_le_of_finrank_le cf (by omega)
    have pm : U≤F 5 := eq.ge
    have g:=clock_invariant_outgoing ha (ps.mono (by omega : 5≤q)) pm Ul
    change finrank K U+3≤finrank K (F 6) at g
    have d:=Submodule.finrank_mono cf
    have p:=up 6 (by decide) (by omega)
    omega
  let J (j:ℕ):Submodule K ((Fin s→K)):=F j⊔U
  have Jlow (j:ℕ) : F j≤J j:=le_sup_left
  have JU (j:ℕ) : U≤J j:=le_sup_right
  have Jin (j:ℕ) (hi:j≤q) : J j≤F q:=sup_le (zeroSpace_mono A hi) Ui
  have Jmap (j:ℕ) : (J j).map C≤J (j+1) := by
    change (F j⊔U).map C≤F (j+1)⊔U
    rw [Submodule.map_sup]
    exact sup_le ((Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A j)).trans le_sup_left)
      (Ul.trans le_sup_right)
  have Jmore (j:ℕ) (lo:5≤j) (hi:j≤q) : ¬J j≤U := by
    intro ne
    exact non5 ((zeroSpace_mono A lo).trans ((Jlow j).trans ne))
  have Jstrict (j:ℕ) (lo:5≤j) (hi:j<q) : J j<J (j+1) := by
    refine lt_of_le_of_ne (sup_le_sup (zeroSpace_mono A (by omega)) le_rfl) (fun e=>?_ )
    exact Jmore j lo hi.le (maxU _ ((Jmap j).trans (le_of_eq e.symm)) (Jin j hi.le))
  have Jgrowth (j r:ℕ) (lo:5≤j) (hi:j+r≤q) : finrank K (J j)+r≤finrank K (J (j+r)) := by
    induction r with
    | zero => exact le_rfl
    | succ r ih =>
      have h:=Submodule.finrank_lt_finrank_of_lt (Jstrict (j+r) (by omega) (by omega))
      have d:=ih (by omega)
      change finrank K (J j)+(r+1)≤finrank K (J (j+r+1))
      omega
  have Jcap (j:ℕ) (lo:5≤j) (hi:j≤q) : finrank K (J j)≤j+1 := by
    have a:=Jgrowth j (q-j) lo (by omega)
    rw [show j+(q-j)=q by omega] at a
    have h:=Submodule.finrank_mono (Jin q le_rfl)
    change finrank K (J q)≤finrank K (zeroSpace A q) at h
    omega
  have Jr5:=Submodule.finrank_mono (Jlow 5)
  have JU5:U<J 5 := lt_of_le_of_ne (JU 5) (fun e=>Jmore 5 (by omega) (by omega) (le_of_eq e.symm))
  have Jf5:=Submodule.finrank_lt_finrank_of_lt JU5
  have Jr6:=Submodule.finrank_lt_finrank_of_lt (Jstrict 5 (by omega) (by omega))
  change finrank K (J 5)<finrank K (J 6) at Jr6
  have j5Cap:=Jcap 5 (by omega) (by omega)
  have j6Cap:=Jcap 6 (by omega) (by omega)
  have same : H=U := by
    apply Submodule.eq_of_le_of_finrank_le HU
    by_contra! ex
    have u5:finrank K U=5:=by omega
    have dJ5:finrank K (J 5)=6:=by omega
    have dJ6:finrank K (J 6)=7:=by omega
    have HH: H<U := lt_of_le_of_ne HU (fun e=>ex.not_ge (by rw [e]))
    have lose:¬U≤H := fun e=>not_lt_of_ge e HH
    obtain ⟨w,wu,wh⟩:=Set.not_subset.mp lose
    have W : ∃i,visible i∧w i≠0 := by
      by_contra! none
      exact wh (detect w (Ui wu) none)
    obtain ⟨i,iv,iw⟩:=W
    let B:=U⊓LinearMap.ker (LinearMap.proj i)
    have bh:H≤B:=le_inf HU (fun _ hv=>blind _ hv i iv)
    have btest:¬U≤B:=fun e=>iw (e wu).2
    have bU:B<U:=lt_of_le_of_ne inf_le_left (fun e=>btest (le_of_eq e.symm))
    have rd:=Submodule.finrank_lt_finrank_of_lt bU
    have be:H=B:=Submodule.eq_of_le_of_finrank_le bh (by omega)
    have support (v:(Fin s→K)) (hu:v∈U) : ∃a,∀l,visible l→nodes A l≠a→v l=0 := by
      refine ⟨nodes A i,fun l lv bad=>?_⟩
      have bp:C v-nodes A i•v∈B := by
        refine ⟨U.sub_mem (Ul (Submodule.mem_map_of_mem hu)) (U.smul_mem _ hu),?_⟩
        change nodes A i*v i-nodes A i*v i=0
        exact sub_self _
      have bpH:=be.symm ▸ bp
      have z:=blind _ bpH l lv
      change nodes A l*v l-nodes A i*v l=0 at z
      exact (mul_eq_zero.mp (show (nodes A l-nodes A i)*v l=0 by linear_combination z)).resolve_left
        (sub_ne_zero.mpr bad)
    have local6:F 6⊓U≤H:=fun _ hv=>oneSite _ hv.1 (support _ hv.2)
    have local5:F 5⊓U≤H:= (inf_le_inf (zeroSpace_mono A (by decide : 5≤6)) le_rfl).trans local6
    have R5:=Submodule.finrank_sup_add_finrank_inf_eq (F 5) U
    change finrank K (J 5)+finrank K ↥(F 5⊓U)=_ at R5
    have eq5:=Submodule.eq_of_le_of_finrank_le local5 (by omega)
    have H5:H≤F 5:=eq5.symm.le.trans inf_le_left
    have g:=clock_invariant_outgoing ha (ps.mono (by omega : 5≤q)) H5 invH
    change finrank K H+3≤finrank K (F 6) at g
    have fc:=up 6 (by decide) (by omega)
    have R6:=Submodule.finrank_sup_add_finrank_inf_eq (F 6) U
    change finrank K (J 6)+finrank K ↥(F 6⊓U)=_ at R6
    have nz:=Submodule.finrank_mono local6
    omega
  have close (j:ℕ) (small:j=5∨j=6) (rank:finrank K (J j)=j+1) : False := by
    have lo:5≤j:=by rcases small with e|e <;> omega
    have hi:j<q:=by rcases small with e|e <;> omega
    have B:finrank K ↥(J j⊔(J j).map C)≤finrank K (J j)+1 := by
      have b:=Submodule.finrank_mono (sup_le (le_of_lt (Jstrict j lo hi)) (Jmap j))
      have c:=Jcap (j+1) (by omega) (by omega)
      omega
    have escape:¬(J j).map C≤J j:=fun e=>Jmore j lo hi.le (maxU _ e (Jin j hi.le))
    obtain ⟨r,W,w,_,Wi,WJ,wm,_,power,last,rd⟩:=single_head B escape
    have UW:U≤W:=wm U Ul (JU j)
    have WU:W≤U:=maxU W Wi (WJ.trans (Jin j hi.le))
    have eq:W=H:=(le_antisymm WU UW).trans same.symm
    have rr:r=j-3:=by rw [eq,dimH,rank] at rd;omega
    have wn:w∈H := by
      apply drop j small w
      intro a ha
      rw [same]
      exact power a (by omega)
    have iterate (n : ℕ) : (C^n) w∈U := by
      induction n with
      | zero => simpa only [pow_zero,one_apply_eq_self] using (same ▸ wn : w∈U)
      | succ n ih => rw [pow_succ',mul_apply_eq_comp]; exact Ul (Submodule.mem_map_of_mem ih)
    exact last (JU j (iterate r))
  by_cases six:finrank K (J 5)=6
  · exact close 5 (Or.inl rfl) six
  have five:finrank K (J 5)=5:=by omega
  have F5J:F 5=J 5:=Submodule.eq_of_le_of_finrank_le (Jlow 5) (by omega)
  have H5:H≤F 5:=(HU.trans (JU 5)).trans F5J.ge
  have g:=clock_invariant_outgoing ha (ps.mono (by omega : 5≤q)) H5 invH
  change finrank K H+3≤finrank K (F 6) at g
  have fx:=Submodule.finrank_mono (Jlow 6)
  exact close 6 (Or.inr rfl) (by omega)

end RKResearch.Certified.Graded
