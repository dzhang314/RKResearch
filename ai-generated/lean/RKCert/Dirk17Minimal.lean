module
public import RKCert.Dirk17Unanchored
public import RKCert.DirkTerminalDelete
public import RKCert.DirkEvenHiddenPort
@[expose] public section
namespace RKCert.Paired.Seventeen
open Module Terminal
variable {K:Type*} [Field K] [CharZero K] {A:Fin 23→Fin 23→K} {b:Vec K 23}
noncomputable section
set_option maxRecDepth 4000

structure Minimal (A:Fin 23→Fin 23→K) (b:Vec K 23):Prop where
  origin:∀i,A 0 i=0
  T:PhysicalTerminal (s:=22) A b
  D:PaidReverseBand (s:=22) A b 17 8
  zero:∀v∈zeroSpace A 5,v (Fin.last 22)=0
  dual:annih (dirkBack A b 6)=treeSpace A 8⊔K ∙ terminalCardinal K 22

/-- The minimal original grade-five mark forces a genuine nonzero terminal
row, and the *terminal-zero* grade-eight flag is exactly the six-dimensional
backward flag. Full M8 is one dimension larger, not the six-word flag. -/
theorem minimal (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17)
    (anc:q₂ (mat A) (nodes A) 1=0) (minimal5:finrank K (marked A 17 5)≤3):Minimal A b:=by
  let t:=Fin.last 22
  let M:=markedTerminalZero (s:=22) A 17
  have org:=dirk_first_row ha anc
  have R:=ranks ha ho
  have E8:finrank K (treeSpace A 8)=16:=by rw [R.e8];simp [excess,anc]
  have d23:=Submodule.finrank_lt_finrank_of_lt (marked_strict ha ho (j:=2) (by decide) (by decide))
  have d34:=Submodule.finrank_lt_finrank_of_lt (marked_strict ha ho (j:=3) (by decide) (by decide))
  have d45:=Submodule.finrank_lt_finrank_of_lt (marked_strict ha ho (j:=4) (by decide) (by decide))
  change finrank K (marked A 17 2)<finrank K (marked A 17 3) at d23
  change finrank K (marked A 17 3)<finrank K (marked A 17 4) at d34
  change finrank K (marked A 17 4)<finrank K (marked A 17 5) at d45
  have bot:marked A 17 2=⊥:=Submodule.finrank_eq_zero.mp (by omega)
  have z1:=marked_mono A 17 (by decide:1≤2) (seed1_marked ho (by decide))
  have z2:=seed2_marked ho (by decide)
  rw [bot] at z1 z2
  have d1:backSeed1 A b=0:=by simpa using z1
  have d2:q₂ (transMat A) (mirror A) b=0:=by simpa using z2
  let T:=terminal_diag_from_seeds (s:=22) ha (true_last ha ho) d1 d2
  have notmem:=first_row_anchored_terminal_not_mem ho (m:=8) (by decide) T org
  have strict:M 8<marked A 17 8:=by
    refine lt_of_le_of_ne inf_le_left (fun eqn=>notmem ?_)
    have prior:M 8≤prior t:=inf_le_right
    rw [eqn] at prior
    have x:=terminal_cardinal_annihilates prior
    rwa [marked,annih_annih_paired] at x
  have top:finrank K (M 8)≤6:=by
    have h:=Submodule.finrank_lt_finrank_of_lt strict
    have cost:=marked_rank A 17 8
    change finrank K (treeSpace A 8)+finrank K (marked A 17 8)=23 at cost
    rw [E8] at cost
    have seven:finrank K (marked A 17 8)=7:=by omega
    have bound:finrank K (M 8)<7:=h.trans_le seven.le
    omega
  have gain (j n:ℕ) (lo:2≤j)(hi:j+n≤8):finrank K (M j)+n≤finrank K (M (j+n)):=by
    induction n with
    | zero=>simp
    | succ n ih=>
      have prev:=ih (by omega)
      have step:=Submodule.finrank_lt_finrank_of_lt (markedTerminalZero_strict ha ho T (j:=j+n) (by omega) (by omega))
      change finrank K (M (j+n))<finrank K (M (j+n+1)) at step
      rw [show j+(n+1)=j+n+1 by omega];omega
  have rank (j:ℕ)(lo:2≤j)(hi:j≤8):finrank K (M j)=j-2:=by
    have cc:=gain j (8-j) lo (by omega)
    rw [Nat.add_sub_of_le hi] at cc
    have inc:=Submodule.finrank_mono (back_sub_markedTerminalZero ha ho T lo (by omega:j+1≤17))
    change finrank K (dirkBack A b (j-2))≤finrank K (M j) at inc
    have lb:=dirkBack_rank ha ho (j-2) (by omega)
    omega
  have words(j:ℕ)(lo:2≤j)(hi:j≤8):M j=dirkBack A b (j-2):=by
    have lp:=rank j lo hi
    have lb:=dirkBack_rank ha ho (j-2) (by omega)
    exact (Submodule.eq_of_le_of_finrank_le (back_sub_markedTerminalZero ha ho T lo (by omega)) (lp.le.trans ((Nat.le_add_right _ _).trans lb))).symm
  have col (i:Fin 23):A i t=0:=by
    have e:=congrFun T.annihilated i
    simpa [t,terminalCardinal,mat_apply,Pi.single_apply,mul_ite] using e
  have full5:M 5=marked A 17 5:=Submodule.eq_of_le_of_finrank_le inf_le_left (minimal5.trans (rank 5 (by decide) (by decide)).ge)
  have last0(v:Vec K 23)(hv:v∈zeroSpace A 5):v t=0:=by
    have mark:=weights_mul_zeroSpace ho (by decide:5+1≤17) hv
    rw [←full5] at mark
    have q:(b*v) t=0:=(prior_last_iff (s:=22) (u:=b*v)).mp mark.2
    exact (mul_eq_zero.mp q).resolve_left T.weight_ne
  have wr(r:ℕ)(pay:r+2≤8):finrank K (dirkBack A b r)=r:=by
    have d:=rank (r+2) (by omega) pay
    rw [words _ (by omega) pay] at d
    rwa [show r+2-2=r by omega] at d
  have zeroWords(j:ℕ)(lo:2≤j)(hi:j≤8):ReverseHermite.zeroMarked A 17 t j=dirkBack A b (j-2):=by
    rw [←words j lo hi]
    ext x
    change (x∈marked A 17 j ∧ x t=0) ↔ (x∈marked A 17 j ∧ x∈prior t)
    rw [prior_last_iff]
  let ec:=terminalCardinal K 22
  have es:treeSpace A 8≤annih (M 8):=annih_flip_le (show M 8≤marked A 17 8 from inf_le_left)
  have ee:ec∈annih (M 8):=terminal_cardinal_annihilates (T:=M 8) inf_le_right
  have dual:annih (M 8)=treeSpace A 8 ⊔ K ∙ ec:=by
    symm;apply Submodule.eq_of_le_of_finrank_le (sup_le es ((Submodule.span_singleton_le_iff_mem ..).mpr ee))
    rw [Submodule.finrank_sup_span_singleton notmem]
    have rank8:=rank 8 (by decide) (by decide)
    have bill:finrank K (M 8)+finrank K (annih (M 8))=23:=finrank_annih_eq _
    rw [rank8] at bill
    rw [E8]
    have bound:finrank K (annih (M 8))≤17:=by omega
    exact bound
  exact ⟨org,T,⟨by decide,by decide,T.node_one,col,⟨d1,d2⟩,fun {r}=>wr r,zeroWords⟩,last0,
    words 8 (by decide) (by decide) ▸ dual⟩

/-- With C(2), the origin condition removes a possible ordinary endpoint
component. No length-22 method or deleted-array order is inferred. -/
theorem minimal_joint_inside (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17) (h:Minimal A b):
    jointWithOrigin A b 0≤zeroSpace A 8:=by
  intro v hv
  obtain ⟨⟨wb,wt⟩,origin⟩:=jointWithOrigin_iff.mp hv
  have dual:v∈annih (dirkBack A b 6):=by
    rw [mem_annih];intro w hw
    obtain ⟨P,_,eqn⟩:=h.D.word_polynomial ha ho (h.D.nonlocal_cubic ha ho) (r:=6) (by decide) (by decide) hw
    rw [row_apply];apply Finset.sum_eq_zero;intro i _
    have e:tau A b i*v i=0:=congrFun wt i
    rw [eqn i];linear_combination P.eval (mirror A i)*e
  rw [h.dual] at dual
  exact hidden_mem_defect ho (by decide:2*8+1≤17) h.origin (Fin.last 22) h.T.weight_ne h.T.node_one
    (origin rfl) (fun i=>congrFun wb i) dual
end
end RKCert.Paired.Seventeen
