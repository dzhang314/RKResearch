module

public import RKCert.ReviewedNative.ERK13NativeMarkedFirstGrades
public import RKCert.ReviewedNative.NativeLiveCore
public import RKCert.ReviewedNative.ERK13OrdinarySquareTransport
import RKCert.ReviewedNative.NativeClockChainPeel
import RKCert.ReviewedNative.CausalStage
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Find
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Disjoint grade-four head and the genuine first-X port in a=5

The core is the original maximal clock-invariant core. The representative
is taken from F4 and then cleaned there; all higher bands of the paid
marked chart remain unchanged. -/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse Module RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19→K}
variable {U : Submodule K (Fin 19→K)} {w v : Fin 19→K} {r : ℕ}
variable {G P R Q : K[X]}
set_option maxHeartbeats 1600000
set_option maxRecDepth 2300

theorem band_core_le (n : ℕ) : U≤escapeHeadBand A U w n :=
  ((clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) n).mp le_rfl).1

theorem band_power_mem {n k : ℕ} (hlt : k<n) :
    ((diag (nodes A))^k) w∈escapeHeadBand A U w n :=
  ((clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) n).mp le_rfl).2 k hlt

theorem band_weighted_mem {n : ℕ} (d : P.natDegree<n) :
    weightedEval (nodes A) w P∈escapeHeadBand A U w n := by
  rw [P.as_sum_range' n d,map_sum]
  apply (escapeHeadBand A U w n).sum_mem
  intro i hi
  have e : weightedEval (nodes A) w (monomial i (P.coeff i))=
      P.coeff i • (((diag (nodes A))^i) w) := by
    funext j
    simp only [weightedEval_apply,eval_monomial,HeadFiber.clock_power_value,
      Pi.smul_apply,smul_eq_mul,mul_assoc]
  rw [e]
  exact (escapeHeadBand A U w n).smul_mem _ (band_power_mem (Finset.mem_range.mp hi))

theorem band_polynomial_repr {n : ℕ} (pos : 0<n)
    (hv : v∈escapeHeadBand A U w n) :
    ∃ u∈U, ∃ S : K[X], S.natDegree<n ∧ v=u+weightedEval (nodes A) w S := by
  obtain ⟨u,hu,S,ds,eq⟩ := HeadFiber.exists_poly hv
  refine ⟨u,hu,S,?_,eq⟩
  by_cases z : S=0
  · simpa only [z,natDegree_zero] using pos
  · exact (natDegree_lt_iff_degree_lt z).mpr ds

theorem coordinate_last_apply_zero {i : Fin 19} (h : i≠Fin.last 18) :
    coordinate (K:=K) (Fin.last 18) i=0 :=
  @Pi.single_eq_of_ne (Fin 19) (fun _=>K) _ (Classical.decEq _)
    (Fin.last 18) i h 1

theorem NativeMarkedEscapeChart.degree_six_terminal_mem
    (H : NativeMarkedEscapeChart A b 5 G r U w)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) :
    coordinate (K:=K) (Fin.last 18)∈treeSpace A 7 :=
  terminal_enters_seven_of_first_degree_six13 ha ho H.seed H.first

theorem NativeMarkedEscapeChart.degree_six_tree_eq_marked
    (H : NativeMarkedEscapeChart A b 5 G r U w)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) {j : ℕ} (lo : 7≤j) :
    markedTreeSpace A b j=treeSpace A j := by
  rw [markedTreeSpace, terminalMark, if_pos H.seed, sup_eq_left]
  exact (Submodule.span_singleton_le_iff_mem ..).mpr
    (treeSpace_mono A lo (H.degree_six_terminal_mem ha ho))

private theorem grade_four_head_of_paid (H : NativePaidHead A b r U w)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (rankFour : finrank K (zeroSpace A 4)=4) :
    ∃ f, U≤zeroSpace A 4 ∧ zeroSpace A 4=escapeHeadBand A U f (r-1) ∧
      ∀ n, r≤n → escapeHeadBand A U f n=escapeHeadBand A U w n := by
  let D := diag (nodes A)
  have stable : U.map D≤U := H.head.coreStable
  have five := H.five
  have six : finrank K (zeroSpace A 6) = 6 := H.midpoint.middleDefects
  have lo := H.headBounds.1
  have base : finrank K (zeroSpace A 5)=finrank K U+r := H.head.baseRank
  obtain ⟨q,V,f,J⟩ := flat_clock_head ha (j:=4) (d:=2)
    (coeff_separated ho (q:=6) (by decide)) (by decide) (by decide)
    (by change finrank K (zeroSpace A 6)≤finrank K (zeroSpace A 4)+2; omega)
  have f4 : zeroSpace A 4=escapeHeadBand A V f q := by
    simpa only [Nat.add_zero] using J.flags 0 (by decide)
  have f5 : zeroSpace A 5=escapeHeadBand A V f (q+1) := J.flags 1 (by decide)
  have f6 : zeroSpace A 6=escapeHeadBand A V f (q+2) := J.flags 2 (by decide)
  have unpaid : (D^(q+1)) f∉escapeHeadBand A V f (q+1) := by
    intro h
    have same : escapeHeadBand A V f (q+2)=escapeHeadBand A V f (q+1) := by
      change escapeHeadBand A V f (q+1) ⊔ (K ∙ ((D^(q+1)) f))=_
      exact sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem ..).mpr h)
    have flags := f6.trans (same.trans f5.symm)
    have dims := congrArg (fun W : Submodule K (Fin 19→K)=>finrank K W) flags
    rw [six,five] at dims
    omega
  have coreFour : U≤zeroSpace A 4 := by
    intro y hy
    have y5 := H.head.coreInside hy
    have cy5 := H.head.coreInside (stable (Submodule.mem_map_of_mem hy))
    rw [f5] at y5 cy5
    rw [f4]
    exact clock_chain_drop_of_next_unpaid J.coreStable q unpaid y5 cy5
  have same : V=U := le_antisymm
    (H.head.coreMaximal V J.coreStable
      (J.coreInside.trans (zeroSpace_mono A (by decide : 4≤5))))
    (J.coreMaximal U stable coreFour)
  subst V
  have rq := J.baseRank
  have qr : q+1=r := by omega
  have old5 : zeroSpace A 5=escapeHeadBand A U w r := by
    simpa only [Nat.add_zero] using H.head.flags 0 (by decide)
  have start : escapeHeadBand A U f r=escapeHeadBand A U w r := calc
    _ = zeroSpace A 5 := by rw [←qr]; exact f5.symm
    _ = _ := old5
  have higher (m : ℕ) : escapeHeadBand A U f (r+m)=escapeHeadBand A U w (r+m) := by
    induction m with
    | zero => simpa only [Nat.add_zero] using start
    | succ m ih =>
      change chain D U f ((r+m)+1) = chain D U w ((r+m)+1)
      change chain D U f (r+m) = chain D U w (r+m) at ih
      rw [←clock_chain_next (w:=f) (n:=r+m) stable (by omega),
        ←clock_chain_next (w:=w) (n:=r+m) stable (by omega), ih]
  exact ⟨f,coreFour,by simpa only [show q=r-1 by omega] using f4,
    fun n hn=>by simpa only [show r+(n-r)=n by omega] using higher (n-r)⟩

private theorem core_times_paid_four (H : NativeMarkedEscapeChart A b 5 G r U w)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) (inside : U≤zeroSpace A 4)
    {x y : Fin 19→K} (hx : x∈U) (hy : y∈zeroSpace A 4) : x*y∈U := by
  let c := nodes A
  have stable := H.head.head.coreStable
  have mask := clock_mask_invariant (fun z (hz : z∈U)=>stable (Submodule.mem_map_of_mem hz))
  let f (a : K) := blockMask c a x*y
  have each (a : K) : f a∈U := by
    have h : f a∈zeroSpace A 8 :=
      zeroSpace_mul (m:=4) (n:=4) (inside (mask a x hx)) hy
    apply H.one_clock_local ha ho (j:=8) (Or.inr rfl) h (t:=a)
    intro i hi
    have d : c i≠a := hi
    simp only [f,Pi.mul_apply,blockMask,if_neg d,zero_mul]
  have all : assembleBlocks c f=x*y := by
    funext i
    rw [assembleBlocks_apply]
    change (blockMask c (c i) x) i*y i=x i*y i
    simp only [blockMask, if_true]
  exact all ▸ assembleBlocks_mem c mask f each

/-- This works for both radii, with no purity premise on the whole F7. -/
structure LobattoCleanHead (A : Matrix (Fin 19) (Fin 19) K)
    (b : Fin 19→K) (r : ℕ) (U : Submodule K (Fin 19→K))
    (old head : Fin 19→K) (G : K[X]) : Prop where
  original : NativeMarkedEscapeChart A b 5 G r U old
  gradeFour : zeroSpace A 4=escapeHeadBand A U head (r-1)
  coreFour : U≤zeroSpace A 4
  headFour : head∈zeroSpace A 4
  headLast : head (Fin.last 18)=0
  coreClosed : ∀ u∈U, ∀ v∈U, u*v∈U
  clean : ∀ i, LiveCore.live U i → head i=0
  same : ∀ n, r≤n → escapeHeadBand A U head n=escapeHeadBand A U old n

theorem NativeMarkedEscapeChart.clean_lobatto_head
    (H : NativeMarkedEscapeChart A b 5 G r U w)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) :
    ∃ v, LobattoCleanHead A b r U w v G := by
  obtain ⟨f,inside,four,bands⟩ := grade_four_head_of_paid H.head ha ho
    (H.first_grades_of_degree_six ha ho).1
  have pos := H.head.headBounds.1
  have f4 : f∈zeroSpace A 4 := by
    rw [four]
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using
      (band_power_mem (A:=A) (U:=U) (w:=f) (n:=r-1) (k:=0) (by omega))
  have close (u : Fin 19→K) (hu : u∈U) (t : Fin 19→K) (ht : t∈U) : u*t∈U :=
    core_times_paid_four H ha ho inside hu (inside ht)
  obtain ⟨v,off,edge⟩ := HeadFiber.disjoint_rep H.head.head.coreStable close
    (fun u hu=>core_times_paid_four H ha ho inside hu f4)
  have vF : zeroSpace A 4=escapeHeadBand A U v (r-1) := four.trans (edge _).symm
  have v4 : v∈zeroSpace A 4 := by
    rw [vF]
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using
      (band_power_mem (A:=A) (U:=U) (w:=v) (n:=r-1) (k:=0) (by omega))
  have last := early_terminal_zeroSpace_five_last ho H.head.paidRanks.lastActive
    (H.degree_six_terminal_mem ha ho) (zeroSpace_mono A (by decide : 4≤5) v4)
  exact ⟨v,⟨H,vF,inside,v4,last,close,off,fun n hn=>(edge n).trans (bands n hn)⟩⟩

theorem LobattoCleanHead.chart (S : LobattoCleanHead A b r U w v G)
    (m : ℕ) (pay : 6+m≤10) :
    markedTreeSpace A b (6+m)=(coeffEval A 5).range⊔markedEscapeHeadBand A b U v (r+2+m) := by
  rw [markedEscapeHeadBand,S.same _ (by omega)]
  exact S.original.chart m pay

theorem LobattoCleanHead.more_physical_clocks (S : LobattoCleanHead A b r U w v G)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) :
    r+5<(HeadFiber.physicalSites (nodes A) v).card := by
  obtain ⟨ranks,_⟩ := marked_staircase_ranks13 ha ho S.original.head S.original.seed
  refine lt_of_lt_of_le ?_ (Finset.card_le_card (HeadFiber.escape_le_physical (U:=U)))
  apply HeadFiber.more_escape_sites S.original.head.head.coreStable (n:=r+5) (by omega)
  intro inv
  have eq : escapeHeadBand A U v (r+5+1)=escapeHeadBand A U v (r+5) :=
    (clock_chain_next S.original.head.head.coreStable (by omega)).symm.trans (sup_eq_left.mpr inv)
  have t9 := S.chart 3 (by decide)
  have t10 := S.chart 4 (by decide)
  change markedTreeSpace A b 9=(coeffEval A 5).range⊔
    (escapeHeadBand A U v (r+5)⊔terminalMark A b) at t9
  change markedTreeSpace A b 10=(coeffEval A 5).range⊔
    (escapeHeadBand A U v (r+5+1)⊔terminalMark A b) at t10
  have same : markedTreeSpace A b 10=markedTreeSpace A b 9 := by rw [t10,eq,←t9]
  have a := ranks 9 (by decide) (by decide)
  have d := ranks 10 (by decide) (by decide)
  rw [same,a] at d
  omega

theorem LobattoCleanHead.mesh_repr (S : LobattoCleanHead A b r U w v G)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) :
    ∃ u∈U, ∃ Q : K[X], Q.natDegree≤r+1 ∧
      evalNodes A G=u+weightedEval (nodes A) v Q+G.eval 1 • coordinate (Fin.last 18) := by
  obtain ⟨d,hd,form⟩ := S.original.early_mesh_exact_mark ha ho
    (S.original.degree_six_terminal_mem ha ho)
  rw [←S.same _ (by omega)] at hd
  obtain ⟨u,hu,Q,qd,q⟩ := band_polynomial_repr (by omega) hd
  exact ⟨u,hu,Q,by omega,by rw [form,q]⟩

/-- A pure square exit needs only this grade-five transport, not the
possibly impure grade-seven defect flag. -/
theorem LobattoCleanHead.pure_first_X_port (S : LobattoCleanHead A b r U w v G)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (rd : R.natDegree≤4) (rn : R≠0) (factor : G=R*Q)
    (amp : ∀ i, v i≠0 → v i=R.eval (nodes A i))
    (mesh : ∃ u∈U, evalNodes A G=u+weightedEval (nodes A) v Q+
      G.eval 1 • coordinate (Fin.last 18)) :
    ∃ i : Fin 19, i<Fin.last 18 ∧ nodes A i≠0 ∧ Q.IsRoot (nodes A i) ∧
      (primitive (X*R)).eval (nodes A i)=0 := by
  let B := X*R
  have bn : B≠0 := mul_ne_zero X_ne_zero rn
  have bd : B.natDegree≤5 := by rw [show B = X * R from rfl, natDegree_X_mul rn]; omega
  obtain ⟨e,he,mask⟩ := LiveCore.exists_live_indicator U S.coreClosed
  let p : Fin 19→K := fun i=>B.eval (nodes A i)*e i
  let y := diag (nodes A) v+p
  let z := evalNodes A B-y
  have pU : p∈U := clock_function_mem
    (fun _ hx=>S.original.head.head.coreStable (Submodule.mem_map_of_mem hx)) B.eval he
  have y5 : y∈zeroSpace A 5 := (zeroSpace A 5).add_mem
    (diag_zeroSpace A 4 S.headFour) (zeroSpace_mono A (by decide : 4≤5) (S.coreFour pU))
  have z5 : z∈treeSpace A 5 := (treeSpace A 5).sub_mem (evalNodes_mem_treeSpace A B bd)
    (zeroSpace_le_treeSpace A 5 y5)
  have zn : z≠0 := by
    intro zero
    have h : evalNodes A B∈zeroSpace A 5 := (sub_eq_zero.mp zero).symm ▸ y5
    exact bn (eval_eq_zero_of_coeff_separated (coeff_separated ho (q:=5) (by decide)) B bd h)
  have ex : ∃ k : ℕ, ∃ i : Fin 19, i.val=k ∧ z i≠0 := by
    by_contra no
    exact zn (funext (fun i=>not_not.mp (fun h=>no ⟨i.val,i,rfl,h⟩)))
  obtain ⟨i,ik,iz⟩ := Nat.find_spec ex
  have pre (h : Fin 19) (hi : h < i) : z h=0 := by
    by_contra hn
    have small : h.val<Nat.find ex := by rw [←ik]; exact hi
    exact Nat.find_min ex small ⟨h,rfl,hn⟩
  have iL : i≠Fin.last 18 := by
    intro atL
    subst i
    have eq : z=z (Fin.last 18) • coordinate (K:=K) (Fin.last 18) := by
      funext j
      by_cases jL : j=Fin.last 18
      · subst j; simp only [Pi.smul_apply,smul_eq_mul,coordinate]; simp
      · have zj := pre j (lt_of_le_of_ne (Fin.le_last j) jL)
        rw [zj,Pi.smul_apply,smul_eq_mul,coordinate_last_apply_zero jL,mul_zero]
    rw [eq] at z5
    have scalar := ((treeSpace A 5).smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr iz)).mp z5
    exact (endpoint_coordinate_out ha ho (q:=6) (by decide) _
      S.original.head.paidRanks.lastActive.live
      (S.original.head.paidRanks.lastActive.node_eq_one ha S.original.seed))
      (treeSpace_mono A (by decide : 5≤6) scalar)
  have zi : z i=B.eval (nodes A i)-(nodes A i*v i+B.eval (nodes A i)*e i) := by
    simp only [z,y,p,Pi.sub_apply,Pi.add_apply,evalNodes_apply,diag_apply]
  have dead : ¬LiveCore.live U i := by
    intro live
    apply iz
    rw [zi,S.clean _ live,mask i,if_pos live,mul_zero,zero_add,mul_one,sub_self]
  have vz : v i=0 := by
    by_contra nonzero
    apply iz
    rw [zi,amp _ nonzero,mask i,if_neg dead,show B = X * R from rfl,eval_mul,eval_X,mul_zero,add_zero,sub_self]
  have bz : B.eval (nodes A i)≠0 := by
    simpa only [zi,vz,mask i,if_neg dead,mul_zero,add_zero,sub_zero] using iz
  have tz : nodes A i≠0 := by
    intro t
    exact bz (by rw [show B = X * R from rfl,eval_mul,eval_X,t,zero_mul])
  have rz : R.eval (nodes A i)≠0 := by
    intro t
    exact bz (by rw [show B = X * R from rfl,eval_mul,t,mul_zero])
  obtain ⟨u,hu,ge⟩ := mesh
  have g0 : G.eval (nodes A i)=0 := by
    simpa only [evalNodes_apply,Pi.add_apply,weightedEval_apply,Pi.smul_apply,smul_eq_mul,
      LiveCore.val_eq_zero_of_not_live dead hu,vz,coordinate_last_apply_zero iL,mul_zero,
      add_zero] using congrFun ge i
  have qi : Q.IsRoot (nodes A i) := by
    change Q.eval (nodes A i)=0
    rw [factor,eval_mul] at g0
    exact (mul_eq_zero.mp g0).resolve_left rz
  have az := causal_mat ha i z (fun j hj=>pre j hj)
  have d : mat A (evalNodes A B)-evalNodes A (primitive B)∈zeroSpace A 6 :=
    primitive_defect A B bd
  have ay : mat A y∈zeroSpace A 6 := mat_zeroSpace_charZero A 5 y5
  have t6 : evalNodes A (primitive B)-mat A z∈zeroSpace A 6 := by
    rw [show evalNodes A (primitive B)-mat A z=
      mat A y-(mat A (evalNodes A B)-evalNodes A (primitive B)) by simp only [z,map_sub]; abel]
    exact (zeroSpace A 6).sub_mem ay d
  have cover : zeroSpace A 6=escapeHeadBand A U v (r+1) := by
    rw [S.same _ (by omega)]
    exact S.original.head.head.flags 1 (by decide)
  rw [cover] at t6
  obtain ⟨u',hu',J,_,ej⟩ := band_polynomial_repr (by omega) t6
  have t0 : (primitive B).eval (nodes A i)=0 := by
    simpa only [evalNodes_apply,Pi.sub_apply,az,sub_zero,Pi.add_apply,weightedEval_apply,
      LiveCore.val_eq_zero_of_not_live dead hu',vz,mul_zero,zero_add] using congrFun ej i
  exact ⟨i,lt_of_le_of_ne (Fin.le_last i) iL,tz,qi,t0⟩

end
end RKResearch.Certified.Graded.ERK13NativeFirst
