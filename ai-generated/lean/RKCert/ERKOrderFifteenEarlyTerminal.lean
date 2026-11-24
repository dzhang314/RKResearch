module
public import RKCert.ERKOrderFifteenLarge
public import RKCert.ERKOrderFifteenEarlyRatio

@[expose] public section

/-! # Native early-terminal leakage and the genuine cubic/quartic head
No assumed stage-rank, head slope, terminal weight, or polynomial moment
is supplied to this proof; all enter from the actual marked chart. -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape Polynomial Module
open scoped Classical
variable {K : Type*} [Field K] [CharZero K] {s a : ℕ}
variable {A : Fin (s+1)→Fin (s+1)→K} {b : Vec K (s+1)}
variable {U : Submodule K (Vec K (s+1))} {w : Vec K (s+1)} {G : K[X]}

omit [CharZero K] in
theorem marked_five_coordinates (ho:HasTreeOrderAtLeast A b 15)
    (S:Saturated A b 7 1) (hterm:terminal (K:=K) s∈treeSpace A 8)
    {z : Vec K (s+1)} (hz:z∈defectPlus A 1 5) :
    ∃ y∈zeroSpace A 5,z=y+z (Fin.last s) • terminal s := by
  obtain ⟨y,hy,t,ht,e⟩ := Submodule.mem_sup.mp hz
  rw [tailPlane,ite_eq_right (by decide : (1:ℕ)≠0)] at ht
  obtain ⟨c,rfl⟩:=Submodule.mem_span_singleton.mp ht
  have ee := congrFun e (Fin.last s)
  have last := terminal_by_nine_zero_five ho S.lastLive (by decide) hterm y hy
  rw [Pi.add_apply,last,Pi.smul_apply,terminal_at_last,smul_eq_mul,mul_one,zero_add] at ee
  exact ⟨y,hy,ee ▸ e.symm⟩

omit [CharZero K] in
theorem marked_five_terminal_probe (ho:HasTreeOrderAtLeast A b 15)
    (S:Saturated A b 7 1) (hterm:terminal (K:=K) s∈treeSpace A 8)
    {z : Vec K (s+1)} (hz:z∈defectPlus A 1 5) :
    probe A b 0 z=b (Fin.last s)*z (Fin.last s) := by
  obtain ⟨y,hy,eq⟩:=marked_five_coordinates ho S hterm hz
  conv_lhs => rw [eq]
  have p : probe A b 0 (terminal s)=b (Fin.last s) := by
    rw [show probe A b 0 (terminal s)=row b (terminal s) by simp [probe],row_terminal]
  rw [map_add,probe_zeroSpace ho (by decide) hy,zero_add,map_smul,p,smul_eq_mul,mul_comm]

theorem marked_five_physical_head (ho:HasTreeOrderAtLeast A b 15) (S:Saturated A b 7 1)
    (M:Margin A b 7 1 1) (C:OddSevenChart A 1 a 2 U w G)
    (hterm:terminal (K:=K) s∈treeSpace A 8) (dis:∀i,Live U i→w i=0) :
    w (Fin.last s)=0 ∧ w∈zeroSpace A 5 ∧ diag (nodes A) w∈zeroSpace A 5 := by
  have core := marked_five_core_two ho S M C.marked
  have tU : tailPlane K s 1≤U := by
    rw [←core]
    exact invariant_le_core (show tailPlane K s 1≤defectPlus A 1 5 from le_sup_right)
      (tail_clock 1 _) 2
  have live : Live U (Fin.last s) := by
    refine ⟨terminal s,tU ?_,by simp [terminal_at_last]⟩
    rw [tailPlane,ite_eq_right (by decide : (1:ℕ)≠0)]
    exact Submodule.mem_span_singleton_self _
  have wL := dis _ live
  have paid (i:ℕ) (hi:i<2) : (diag (nodes A)^i) w∈zeroSpace A 5 := by
    have m := marked_power C.marked (by decide) hi
    obtain ⟨y,hy,e⟩:=marked_five_coordinates ho S hterm m
    rw [pow_diag_apply,wL,mul_zero,zero_smul,add_zero] at e
    exact e.symm ▸ hy
  exact ⟨wL,by simpa only [pow_zero,one_apply_eq_self] using paid 0 (by decide),
    by simpa only [pow_one] using paid 1 (by decide)⟩

theorem early_band_terminal_probe (ho:HasTreeOrderAtLeast A b 15) (S:Saturated A b 7 1)
    (C:OddSevenChart A 1 a 2 U w G)
    (hterm:terminal (K:=K) s∈treeSpace A 8)
    (w0:w (Fin.last s)=0) (w5:w∈zeroSpace A 5)
    {z:Vec K (s+1)} (hz:z∈forwardBand A 7 a 2 U w 10) :
    probe A b 0 z=b (Fin.last s)*z (Fin.last s) := by
  obtain ⟨x,hx,Q,qd,e⟩:=exists_head_poly hz
  have hdeg : Q.natDegree≤7 := by
    by_cases q0:Q=0
    · simp [q0]
    · have l := (natDegree_lt_iff_degree_lt q0).mpr qd
      have alo := C.aLo
      unfold headLen at l
      omega
  have tr : evalNodes A Q∈treeSpace A 7 := evalNodes_mem_treeSpace A Q hdeg
  have qz : evalNodes A Q*w∈zeroSpace A 12 := by
    rw [mul_comm]
    exact zeroSpace_mul_treeSpace ho (n:=7) (by decide) w5 tr
  have eq : z=x+evalNodes A Q*w := by
    ext i
    exact e i
  rw [eq,map_add,probe_zeroSpace ho (by decide) qz,add_zero,Pi.add_apply,Pi.mul_apply,w0,mul_zero,add_zero]
  exact marked_five_terminal_probe ho S hterm (C.marked.core hx)

theorem early_ghost_terminal_ratio (ho:HasTreeOrderAtLeast A b 15) (S:Saturated A b 7 1)
    (M:Margin A b 7 1 1) (C:OddSevenChart A 1 a 2 U w G)
    (hterm:terminal (K:=K) s∈treeSpace A 8)
    (w0:w (Fin.last s)=0) (w5:w∈zeroSpace A 5)
    {v:Vec K (s+1)} (hv:v∈zeroSpace A 10) (vl:v (Fin.last s)=0)
    (P:K[X]) (pd:P.natDegree≤a) (hp:v-evalNodes A P∈forwardBand A 7 a 2 U w 10) :
    terminalMoment (b (Fin.last s)) P=0 := by
  let z := v-evalNodes A P
  have zl : z (Fin.last s)= -P.eval 1 := by
    simp [z,Pi.sub_apply,vl,evalNodes,M.atOne (by decide)]
  have ez := early_band_terminal_probe ho S C hterm w0 w5 hp
  change probe A b 0 z=b (Fin.last s)*z (Fin.last s) at ez
  have sh : v=evalNodes A P+z := by unfold z;abel
  have pr : probe A b 0 v=0 := probe_zeroSpace ho (k:=0) (by decide) hv
  have ad:=C.aLe
  rw [sh,map_add,probe_eval_moment ho P 0 (by omega),ez,zl] at pr
  unfold terminalMoment
  linear_combination pr

set_option maxHeartbeats 1600000 in
theorem early_three_square_band (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 15)
    (S:Saturated A b 7 1) (M:Margin A b 7 1 1) (C:OddSevenChart A 1 a 2 U w G)
    (hterm:terminal (K:=K) s∈treeSpace A 8) (dis:∀i,Live U i→w i=0) :
    ∀k≤2,(diag (nodes A)^k) (w*w)∈forwardBand A 7 a 2 U w 10 := by
  let D := diag (nodes A)
  obtain ⟨w0,w5,wC⟩:=marked_five_physical_head ho S M C hterm dis
  have wCD : D w∈zeroSpace A 5 := wC
  have paid (i:ℕ) (hi:i≤2) : (D^i) (w*w)∈zeroSpace A 10 := by
    interval_cases i
    · simpa only [pow_zero,one_apply_eq_self] using zeroSpace_mul w5 w5
    · have eq : D (w*w)=D w*w := by ext j;simp [D,mul_assoc]
      rw [pow_one,eq]
      exact zeroSpace_mul (m:=5) (n:=5) wCD w5
    · have eq : (D^2) (w*w)=D w*D w := by ext j;simp [D,pow_two];ring
      rw [eq]
      exact zeroSpace_mul (m:=5) (n:=5) wCD wCD
  let B := a-4
  have ale:=C.aLe
  have alo:=C.aLo
  have data (i:ℕ) : ∃ P:K[X],i≤2→P.natDegree≤a ∧ P.coeff 0=0 ∧
      (D^i) (w*w)-evalNodes A P∈forwardBand A 7 a 2 U w 10 ∧
      (∀ k≤B,balancedMoment 1 P k=0) ∧ terminalMoment (b (Fin.last s)) P=0 := by
    by_cases hi:i≤2
    · have F : (D^i) (w*w)∈defectPlus A 1 10 :=
        (show zeroSpace A 10≤defectPlus A 1 10 from le_sup_left) (paid i hi)
      obtain ⟨P,pd,p0,proj,mom⟩:=C.grade_ten_decompose ha ho S M F
      have last : ((D^i) (w*w)) (Fin.last s)=0 := by simp [D,pow_diag_apply,w0]
      exact ⟨P,fun _=>⟨pd,p0,proj,(by simpa [B] using mom),
        early_ghost_terminal_ratio ho S M C hterm w0 w5 (paid i hi) last P pd proj⟩⟩
    · exact ⟨0,fun e=>(hi e).elim⟩
  choose P good using data
  have shift (i:ℕ) (hi:i<2) : ∃t:K,X*P i-P (i+1)=t • G := by
    obtain ⟨dp,_,proj,_⟩:=good i hi.le
    obtain ⟨dq,_,next,_⟩:=good (i+1) (by omega)
    rw [pow_succ',mul_apply_eq_comp] at next
    exact C.shift_poly S M (by omega) (by decide) dp dq proj next
  have gm : ∀k<B+2,balancedMoment 1 G k=0 := by
    intro k hk
    apply C.mesh_moment ho M
    simp
    dsimp [B] at hk
    omega
  have test := consecutive_moments P G B 2 (fun i hi=>(good i hi).2.2.2.1) shift gm
  obtain ⟨t,st⟩:=shift 0 (by decide)
  have init:=good 0 (by decide)
  have step:=good 1 (by decide)
  have tz : P 0=0 := early_marked_scalar_rigid (by omega) C.mesh C.meshDegree init.1 step.1 init.2.1
    (fun k hk=>test k (by dsimp [B];omega)) init.2.2.2.2 step.2.2.2.2 st
  have all0 (i:ℕ) (hi:i≤2) : P i=0 := by
    induction i with
    | zero => exact tz
    | succ i ih =>
      obtain ⟨t,fit⟩:=shift i (by omega)
      rw [ih (by omega),mul_zero,zero_sub] at fit
      by_cases z:t=0
      · simpa only [z,zero_smul,neg_eq_zero] using fit
      · have hdeg := congrArg Polynomial.natDegree fit
        rw [natDegree_neg,natDegree_smul G z,C.meshDegree] at hdeg
        have deg := (good (i+1) hi).1
        omega
  intro k hk
  have hP := (good k hk).2.2.1
  have evz : evalNodes A (0:K[X])=0 := by ext i;simp [evalNodes]
  rwa [all0 k hk,evz,sub_zero] at hP

theorem early_fifteen_profile (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 15)
    (S:Saturated A b 7 1) (M:Margin A b 7 1 1) (C:OddSevenChart A 1 a 2 U w G)
    (hterm:terminal (K:=K) s∈treeSpace A 8) :
    ∃ (v:Vec K (s+1)) (P:K[X]), OddSevenChart A 1 a 2 U v G ∧
      SevenProfile A 2 U v P ∧ P∣G ∧ P.natDegree+3=a := by
  obtain ⟨v,C,alg,dis⟩:=clean_fifteen_head ha ho S M C
  have square := early_three_square_band ha ho S M C hterm dis
  obtain ⟨P,pd,hP⟩:=multiplier_degree (a:=v) (d:=2) dis C.ten_count square
  have pn:P≠0 := by
    intro hz
    have hc:=C.ten_count
    obtain ⟨x,hx⟩:=Finset.card_pos.mp (show 0<(headSites (nodes A) v).card by omega)
    obtain ⟨i,hi,_⟩:=Finset.mem_image.mp hx
    have vn: v i≠0 := (Finset.mem_filter.mp hi).2
    exact vn (by rw [hP _ vn,hz,eval_zero])
  have deg := pd.resolve_left pn
  obtain ⟨Q,eq,_,sum⟩:=fifteen_factor_of_profile S M C dis pn (by omega) hP
  have a7 := C.aLe
  exact ⟨v,P,C,⟨alg,dis,pn,by omega,hP⟩,⟨Q,eq⟩,by omega⟩

end RKCert.Paired.FiniteMidpoint
