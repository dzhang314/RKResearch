module
public import RKCert.Dirk19Terminal
public import RKCert.DirkPaidPorts
public import RKCert.DirkEvenFifthFloor
public import RKCert.DirkEvenHiddenPort
@[expose] public section
namespace RKCert.Paired.Nineteen
open Module Terminal
variable {K:Type*} [Field K] [CharZero K] {A:Fin 26→Fin 26→K} {b:Vec K 26}

omit [CharZero K] in
theorem paid_reverse (T:TerminalBand A b) : PaidReverseBand (s:=25) A b 19 9:=
  ⟨by decide,by decide,T.last.node_one,T.col_zero,⟨T.last.seed1_zero,T.last.seed2_zero⟩,
    fun {r} h=>T.wordRank r h,T.zeroWords⟩

omit [CharZero K] in
/-- A weight-killed ordinary tree vector in a fully paid odd grade is already a defect. -/
theorem weight_killed_tree_is_defect {s p q:ℕ} {B:Fin s→Fin s→K} {β x:Vec K s}
    (ho:HasTreeOrderAtLeast B β p) (pay:2*q+1≤p) (hx:x∈treeSpace B q) (kill:β*x=0) :
    x∈zeroSpace B q:=by
  obtain ⟨a,ha⟩:=exists_poly_zeroSpace ho (by omega) hx
  have zero (k:ℕ):probe B β k x=0:=by
    rw [probe,row_apply]
    apply Finset.sum_eq_zero;intro i _
    have h:β i*x i=0:=congrFun kill i
    calc β i*(nodes B i)^k*x i=(β i*x i)*(nodes B i)^k:=by ring
         _=0:=by rw [h,zero_mul]
  have az:a=0:=by
    funext j
    apply moments_detect ho (d:=1) (by decide) (by omega) (fun i l=>by omega) a _ j
    intro i
    have e:probe B β i.val (x - polyEval B q a)=0:=probe_zeroSpace ho (by omega) ha
    rw [map_sub,zero,zero_sub,neg_eq_zero,probe_polyEval ho (by omega)] at e
    exact e
  simpa [az] using ha

/-- A native backward word is a polynomial times the cubic output port.
Pointwise annihilation of that port therefore kills the entire word space. -/
theorem tau_kills_paid_words {s p H r:ℕ} {B:Fin (s+1)→Fin (s+1)→K} {β v:Vec K (s+1)}
    (D:PaidReverseBand B β p H) (ha:LowerArray B) (ho:HasTreeOrderAtLeast B β p)
    (lo:1≤r) (hi:r≤H-2) (kill:tau B β*v=0) : v∈annih (dirkBack B β r):=by
  apply (mem_annih (U:=dirkBack B β r) (u:=v)).mpr
  intro y hy
  obtain ⟨P,_,eqn⟩:=D.word_polynomial ha ho (D.nonlocal_cubic ha ho) lo hi hy
  rw [row_apply];apply Finset.sum_eq_zero;intro i _
  change v i*y i=0
  have h:tau B β i*v i=0:=congrFun kill i
  rw [eqn,mul_left_comm,mul_comm (v i),h,mul_zero]

/-- The common coordinatewise annihilator of the two actual rows is invariant.
On the terminal-extension branch its first coordinate is set to zero as well,
so that it belongs to the true defect space rather than its terminal extension. -/
theorem hidden_space (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 19) :
    ∃W:Submodule K (Vec K 26),zeroSpace A 4≤W ∧ W≤zeroSpace A 9 ∧ W.map (diag (nodes A))≤W:=by
  classical
  let R:=initial_ranks ha ho
  let T:=terminal_band ha ho
  have D:PaidReverseBand (s:=25) A b 19 9:=paid_reverse T
  have hidden(v:Vec K 26)(hv:v∈zeroSpace A 4): b*v=0 ∧ tau A b*v=0:=
    D.quartic_jointly_hidden ha ho (by decide) hv (T.f9_zero v (zeroSpace_mono A (by decide:4≤9) hv))
  have dual(v:Vec K 26)(ht:tau A b*v=0):v∈annih (dirkBack A b 7):=by
    simpa only [Nat.reduceAdd] using tau_kills_paid_words (s:=25) D ha ho (by decide:1≤7) (by decide) ht
  by_cases anc:q₂ (mat A) (nodes A) 1=0
  · have origin:=dirk_first_row ha anc
    refine ⟨jointKernel (s:=25) A b,?_,?_,invariant_joint⟩
    · intro v hv;exact joint_iff.mpr ⟨⟨zeroSpace_first_of_row origin 4 hv,(hidden v hv).1⟩,(hidden v hv).2⟩
    · intro v hv;obtain ⟨⟨v0,hb⟩,ht⟩:=joint_iff.mp hv
      have inc:=dual v ht
      rw [T.dual_nine] at inc
      exact hidden_mem_defect ho (by decide:2*9+1≤19) origin (Fin.last 25) T.last.weight_ne
        T.last.node_one v0 (fun i=>congrFun hb i) inc
  · have ex:excess A=1:=by simp [excess,anc]
    let W:=LinearMap.ker (diag b) ⊓LinearMap.ker (diag (tau A b))
    have incl:treeSpace A 9≤annih (dirkBack A b 7):=by rw [T.dual_nine];exact le_sup_left
    have eqn:treeSpace A 9=annih (dirkBack A b 7):=by
      apply Submodule.eq_of_le_of_finrank_le incl
      have wr:=T.wordRank 7 (by decide)
      have dim:finrank K (dirkBack A b 7)+finrank K (annih (dirkBack A b 7))=26:=finrank_annih_eq _
      have e:=R.e9;rw [ex] at e;omega
    refine ⟨W,fun v hv=>hidden v hv,?_,?_⟩
    · intro v hv
      exact weight_killed_tree_is_defect ho (by decide:2*9+1≤19) (eqn ▸ dual v hv.2) hv.1
    · rintro _ ⟨v,⟨hb,ht⟩,rfl⟩
      change b*v=0 at hb;change tau A b*v=0 at ht
      change b*(nodes A*v)=0 ∧ tau A b*(nodes A*v)=0
      constructor <;> rw [mul_left_comm] <;> simp [hb,ht]
end RKCert.Paired.Nineteen
