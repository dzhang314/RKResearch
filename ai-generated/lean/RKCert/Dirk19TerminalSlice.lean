module
public import RKCert.Dirk19Terminal
public import RKCert.DirkNineRankDispatch
public import RKCert.EndpointTailMoments
@[expose] public section
namespace RKCert.Paired.Nineteen
open Module Polynomial Terminal RKCert.Endpoint
variable {K:Type*} [Field K] [CharZero K] {A:Fin 26→Fin 26→K} {b:Vec K 26}

/-- A genuine tenth-grade residual has nonzero final coordinate. Otherwise
the final clock 1 refunds a scalar moment on both cubic-seed branches;
the anchored branch refunds the zero clock as well. -/
theorem ten_not_all_terminal_zero (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 19) :
    ¬∀v∈zeroSpace A 10,v (Fin.last 25)=0:=by
  classical
  let R:=initial_ranks ha ho
  let T:=terminal_band ha ho
  intro clean
  have tests (H:K[X]) (dH:H.natDegree≤10) (v:evalNodes A H∈zeroSpace A 10) (k:ℕ) (hk:k≤8):
      tailMoment k H=0:=by
    have zero:=probe_zeroSpace ho (by omega:k+10+1≤19) v
    have e:=(OrdinaryTrace.scalar A dH).probe ho k (by omega)
    change probe A b k (evalNodes A H)=0 at zero
    rw [e,formalPrimitive_eq_treePrimitive] at zero
    exact zero
  have last (H:K[X]) (v:evalNodes A H∈zeroSpace A 10) : H.eval 1=0:=by
    have c:=clean _ v
    rwa [evalNodes_apply,T.last.node_one] at c
  have convert {q:ℕ} (pdet:∀H:K[X],H.natDegree≤q→evalNodes A H∈zeroSpace A 10→H=0)
      (a:Fin (q+1)→K) (ha:polyEval A q a∈zeroSpace A 10):a=0:=by
    let H:=ofFn (q+1) a
    have deg:H.natDegree≤q:=Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) a)
    have hz:H=0:=pdet H deg (by change evalNodes A (ofFn (q+1) a)∈_;rwa [evalNodes_ofFn])
    funext j
    change a j=0
    rw [←ofFn_coeff_eq_val_of_lt a j.isLt]
    change H.coeff j.val=0
    rw [hz,coeff_zero]
  by_cases anc:q₂ (mat A) (nodes A) 1=0
  · have ex:excess A=0:=by simp [excess,anc]
    have origin:=dirk_first_row ha anc
    have inject (H:K[X]) (dh:H.natDegree≤10) (v:evalNodes A H∈zeroSpace A 10):H=0:=by
      apply two_endpoint_moment_detect H dh _ (last H v) (fun j hj=>tests H dh v j (by omega))
      have z:evalNodes A H 0=0:=zeroSpace_first_of_row origin 10 v
      simpa only [evalNodes_apply,show nodes A 0=0 by simp [nodes,origin]] using z
    have grow:=treeSpace_rank_of_delayed (by decide:10≤10) (convert inject)
    have f:=R.f10;rw [ex] at f
    have e:=R.e10;omega
  · have ex:excess A=1:=by simp [excess,anc]
    have inject (H:K[X]) (dh:H.natDegree≤9) (v:evalNodes A H∈zeroSpace A 10):H=0:=by
      apply endpoint_moment_detect (m:=9) (by decide) H dh (Or.inr (last H v))
      intro B dB
      have sum:=tailMoment_mul 0 B H
      rw [show tailMoment 0 (B*H)=integral (H*B) by simp [tailMoment,mul_comm]] at sum
      rw [sum];apply Finset.sum_eq_zero;intro i hi
      have j:=Finset.mem_range.mp hi
      rw [tests H (by omega) v (0+i) (by omega),mul_zero]
    have grow:=treeSpace_rank_of_delayed (by decide:9≤10) (convert inject)
    have f:=R.f10;rw [ex] at f
    have e:=R.e10;omega

/-- The raised grade-nine clock span is exactly the terminal-zero slice
of the genuine F10. It escapes under one more clock and contains all F5·F5. -/
theorem raised_nine_slice (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 19) :
    raisedNine A=zeroSpace A 10 ⊓ LinearMap.ker (LinearMap.proj (Fin.last 25)) ∧
    ¬(raisedNine A).map (diag (nodes A))≤raisedNine A ∧
    ∀a∈zeroSpace A 5,∀v∈zeroSpace A 5,a*v∈raisedNine A:=by
  classical
  let R:=initial_ranks ha ho
  let T:=terminal_band ha ho
  let S:=zeroSpace A 10 ⊓ LinearMap.ker (LinearMap.proj (Fin.last 25))
  have sub:raisedNine A≤zeroSpace A 10:=sup_le (zeroSpace_mono A (by decide:9≤10))
    (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A 9))
  have clean:raisedNine A≤LinearMap.ker (LinearMap.proj (Fin.last 25)):=by
    apply sup_le (fun v hv=>T.f9_zero v hv)
    rintro _ ⟨v,hv,rfl⟩
    change nodes A (Fin.last 25)*v (Fin.last 25)=0
    rw [T.f9_zero v hv,mul_zero]
  have introS:raisedNine A≤S:=le_inf sub clean
  have low:zeroSpace A 9<raisedNine A:=by
    apply lt_of_le_of_ne le_sup_left
    intro e
    have inv:(zeroSpace A 9).map (diag (nodes A))≤zeroSpace A 9:=(le_sup_right:_≤raisedNine A).trans e.ge
    have g:=dirk_forward_invariant_incoming ha ho (j:=9) (by decide) (fun v hv=>inv ⟨v,hv,rfl⟩)
    change finrank K (zeroSpace A 8)+4≤finrank K (zeroSpace A 9) at g
    have f:=R.f8;have f':=R.f9;omega
  have upper:S<zeroSpace A 10:=by
    apply lt_of_le_of_ne inf_le_left
    intro eqn
    exact ten_not_all_terminal_zero ha ho (fun v hv=> ((show S=zeroSpace A 10 from eqn).ge hv).2)
  have lb:=Submodule.finrank_lt_finrank_of_lt low
  have ub:=Submodule.finrank_lt_finrank_of_lt upper
  have eqn:raisedNine A=S:=by
    apply Submodule.eq_of_le_of_finrank_le introS
    have f:=R.f9;have f':=R.f10;omega
  have f11:finrank K (zeroSpace A 11)≤12+excess A:=by
    have er:finrank K (treeSpace A 11)=21:=(T.tail 11 5 (by decide) (by decide)).1
    by_cases anc:q₂ (mat A) (nodes A) 1=0
    · have ex:excess A=0:=by simp [excess,anc]
      have sep:=poly_separated_delayed_first (dirk_first_row ha anc) ho (q:=8) (m:=11) (by decide) (by decide)
      have dim:9+finrank K (zeroSpace A 11)≤finrank K (treeSpace A 11):=treeSpace_rank_of_delayed (by decide:8≤11) sep
      rw [ex];omega
    · have ex:excess A=1:=by simp [excess,anc]
      have sep:=poly_separated_delayed ho (q:=7) (m:=11) (by decide) (by decide)
      have dim:8+finrank K (zeroSpace A 11)≤finrank K (treeSpace A 11):=treeSpace_rank_of_delayed (by decide:7≤11) sep
      rw [ex];omega
  refine ⟨eqn,?_,?_⟩
  · intro inv
    have g:=dirk_forward_invariant_outgoing ha ho (j:=10) (by decide) (raisedNine A) sub
      (fun v hv=>inv ⟨v,hv,rfl⟩)
    change finrank K (raisedNine A)+5≤finrank K (zeroSpace A 11) at g
    have f:=R.f9;omega
  · intro a ha' v hv
    rw [eqn];refine ⟨zeroSpace_mul (A:=A) (m:=5) (n:=5) ha' hv,?_⟩
    change a (Fin.last 25)*v (Fin.last 25)=0
    rw [T.f9_zero a (zeroSpace_mono A (by decide:5≤9) ha'),zero_mul]
end RKCert.Paired.Nineteen
