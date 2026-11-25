module

public import RKCert.ReviewedNative.ERK13NativeMarkedLobattoHead
public import RKCert.ReviewedNative.ERK13NativeMarkedLobattoProjection
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The degree-six square exits on actual marked rows

Three paid endpoint differences suffice in the degree-six mesh. The
small transported square is treated by exact polynomial divisibility,
not a cardinal bound or a split-root assumption. The only residual is
the literal degree-eight transport at radius two. -/

namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse Module RKCert.OneEscape RKCert.Endpoint MarkedAdjacent
open scoped Classical Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19→K}
variable {U : Submodule K (Fin 19→K)} {w v : Fin 19→K} {r : ℕ}
variable {G P R Q : K[X]}
set_option maxHeartbeats 1700000
set_option maxRecDepth 2300

abbrev lobattoTerminalAxis : Fin 19→K := coordinate (Fin.last 18)

/-- Exactly the scalar premise used by the two native pure exits. No
matrix, support cardinal, or F7-closure premise enters this arithmetic. -/
def LobattoPureFirstCut (K : Type*) [Field K] : Prop :=
  ∀ (R Q : K[X]) (g : K), g≠0 → R.natDegree≤4 →
    R*Q=g • earlyLobattoMesh K →
    ∀ t : K, t≠0 → Q.IsRoot t → (primitive (X*R)).eval t≠0

theorem LobattoCleanHead.impossible_of_factor (S : LobattoCleanHead A b r U w v G)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (cut : LobattoPureFirstCut K)
    (rd : R.natDegree≤4) (rn : R≠0) (factor : G=R*Q)
    (amp : ∀ i,v i≠0 → v i=R.eval (nodes A i))
    (mesh : ∃ u∈U, evalNodes A G=u+weightedEval (nodes A) v Q+
      G.eval 1 • coordinate (Fin.last 18)) : False := by
  obtain ⟨i,_,tn,pivot,van⟩ := S.pure_first_X_port ha ho rd rn factor amp mesh
  obtain ⟨g,gn,meshg⟩ := S.original.degree_six_mesh_is_lobatto ha ho
  exact cut R Q g gn rd (factor.symm.trans meshg) _ tn pivot van

theorem factor_of_clean_lobatto_sites
    (dG : G.natDegree<(HeadFiber.physicalSites (nodes A) v).card)
    (dRQ : R.natDegree+Q.natDegree<(HeadFiber.physicalSites (nodes A) v).card)
    (lastZero : v (Fin.last 18)=0) (clean : ∀ i,LiveCore.live U i → v i=0)
    (amp : ∀ i,v i≠0 → v i=R.eval (nodes A i))
    (mesh : ∃ u∈U, evalNodes A G=u+weightedEval (nodes A) v Q+
      G.eval 1 • coordinate (Fin.last 18)) : G=R*Q := by
  let S := HeadFiber.physicalSites (nodes A) v
  obtain ⟨u,hu,form⟩ := mesh
  apply eq_of_degrees_lt_of_eval_finset_eq S
  · apply degree_le_natDegree.trans_lt
    exact_mod_cast dG
  · apply degree_le_natDegree.trans_lt
    have d := natDegree_mul_le (p:=R) (q:=Q)
    exact_mod_cast (d.trans_lt dRQ)
  · intro t ht
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
    have vi := (Finset.mem_filter.mp hi).2
    have ui : u i=0 := by
      by_contra nz
      exact vi (clean i ⟨u,hu,nz⟩)
    have iL : i≠Fin.last 18 := fun e=>vi (e.symm ▸ lastZero)
    have eq := congrFun form i
    simp only [evalNodes_apply,Pi.add_apply,weightedEval_apply,Pi.smul_apply,smul_eq_mul,
      ui,zero_add,coordinate_last_apply_zero iL,mul_zero,add_zero,amp i vi] at eq
    simpa only [eval_mul,mul_comm] using eq

/-- Radius three supplies all three paid grade-eight square shifts. -/
theorem LobattoCleanHead.radius_three_impossible (S : LobattoCleanHead A b 3 U w v G)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (cut : LobattoPureFirstCut K) : False := by
  let D := diag (nodes A)
  have cv4 : D v∈zeroSpace A 4 := by
    rw [S.gradeFour]
    simpa only [pow_one] using
      (band_power_mem (A:=A) (U:=U) (w:=v) (n:=2) (k:=1) (by decide))
  have sq : v*v∈zeroSpace A 8 := zeroSpace_mul S.headFour S.headFour
  have sq1 : D (v*v)∈zeroSpace A 8 := by
    have e : D (v*v)=v*(D v) := by
      funext i; simp only [D,diag_apply,Pi.mul_apply]; ring
    rw [e]
    exact zeroSpace_mul S.headFour cv4
  have sq2 : D (D (v*v))∈zeroSpace A 8 := by
    have e : D (D (v*v))=(D v)*(D v) := by
      funext i; simp only [D,diag_apply,Pi.mul_apply]; ring
    rw [e]
    exact zeroSpace_mul cv4 cv4
  have shifts (k : ℕ) (h : k≤8-6) : (D^k) (v*v)∈zeroSpace A 8 := by
    have cut : k=0∨k=1∨k=2 := by omega
    rcases cut with rfl|rfl|rfl
    · simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using sq
    · simpa only [pow_one] using sq1
    · simpa only [pow_two,Module.End.mul_eq_comp,LinearMap.comp_apply] using sq2
  have band (k : ℕ) (h : k≤2) : (D^k) (v*v)∈escapeHeadBand A U v 6 := by
    rw [S.same _ (by decide)]
    exact S.original.adjacent_unmarked_pure ha ho (j:=8) (Or.inr rfl) shifts k h
  have many := S.more_physical_clocks ha ho
  obtain ⟨R,rd,amp⟩ := HeadFiber.multiplier_polynomial (n:=6) (d:=2) (a:=v) S.clean
    (by omega : 6<(HeadFiber.physicalSites (nodes A) v).card) band
  have rn : R≠0 := by
    intro z
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0<(HeadFiber.physicalSites (nodes A) v).card by omega)
    obtain ⟨i,hi,_⟩ := Finset.mem_image.mp ha
    have vi := (Finset.mem_filter.mp hi).2
    exact vi (by rw [amp i vi,z,eval_zero])
  obtain ⟨u,hu,Q,qd,ge⟩ := S.mesh_repr ha ho
  have gd : G.natDegree=6 := S.original.first.degree
  have rb := rd.resolve_left rn
  have fac := factor_of_clean_lobatto_sites (G:=G) (R:=R) (Q:=Q) (v:=v)
    (by omega) (by omega) S.headLast S.clean amp ⟨u,hu,ge⟩
  exact S.impossible_of_factor ha ho cut (by omega) rn fac amp ⟨u,hu,ge⟩

/-- Actual radius-two E8 and first mesh expansions, each with its own
exact terminal scalar. These are not a new tableau or chart assumption. -/
structure LobattoSquareSection (A : Matrix (Fin 19) (Fin 19) K)
    (b : Fin 19→K) (U : Submodule K (Fin 19→K))
    (w v : Fin 19→K) (G P R Q : K[X]) : Prop where
  head : LobattoCleanHead A b 2 U w v G
  pd : P.natDegree≤5
  rd : R.natDegree≤5
  qd : Q.natDegree≤3
  p0 : P.eval 0=0
  paid : ∀ k : Fin 3, endpointMoment K k.val P=0
  square : ∃ u∈U, v*v=evalNodes A P+weightedEval (nodes A) v R+u-P.eval 1 • lobattoTerminalAxis
  mesh : ∃ a∈U, evalNodes A G=a+weightedEval (nodes A) v Q+G.eval 1 • lobattoTerminalAxis

theorem LobattoCleanHead.radius_two_square_section (S : LobattoCleanHead A b 2 U w v G)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) :
    ∃ P R Q, LobattoSquareSection A b U w v G P R Q := by
  have v8 : v*v∈zeroSpace A 8 := zeroSpace_mul S.headFour S.headFour
  have v8t : v*v∈markedTreeSpace A b 8 :=
    Submodule.mem_sup_left (zeroSpace_le_treeSpace A 8 v8)
  have e8 := S.chart 2 (by decide)
  rw [e8] at v8t
  obtain ⟨p,hp,d,hd,z⟩ := Submodule.mem_sup.mp v8t
  obtain ⟨P,pd,hP⟩ := exists_polynomial_of_coeff_range hp
  obtain ⟨x,hx,m,hm,dShape⟩ := Submodule.mem_sup.mp hd
  rw [terminalMark,if_pos S.original.seed] at hm
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hm
  obtain ⟨u,hu,R,rd,rShape⟩ := band_polynomial_repr (by decide : 0<6) hx
  have shape : v*v=evalNodes A P+weightedEval (nodes A) v R+u+a • lobattoTerminalAxis := by
    rw [←z,←hP,←dShape,rShape]; abel
  have band9 : x∈zeroSpace A 9 := by
    rw [S.same _ (by decide)] at hx
    exact escapeHeadBand_paid_from_seven S.original.head 2 hx
  have eP : evalNodes A P∈markedDefectSpace A b 9 := by
    change evalNodes A P∈zeroSpace A 9⊔terminalMark A b
    have h : v*v-x∈zeroSpace A 9 :=
      (zeroSpace A 9).sub_mem (zeroSpace_mono A (by decide : 8≤9) v8) band9
    refine Submodule.mem_sup.mpr ⟨v*v-x,h,-a • lobattoTerminalAxis,?_,?_⟩
    · rw [terminalMark,if_pos S.original.seed]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [←z,←hP,←dShape]
      simp only [lobattoTerminalAxis, neg_one_smul, neg_smul]
      abel
  have p0 := origin_of_marked_defect_polynomial ha (by decide) eP
  have tests (k : Fin 3) : endpointMoment K k.val P=0 :=
    endpointMoment_zero_of_marked_defect ha ho S.original.head.paidRanks.lastActive
      (by have := k.isLt; omega) (by have := k.isLt; omega) eP
  have one := S.original.head.paidRanks.lastActive.node_eq_one ha S.original.seed
  have uL := early_terminal_zeroSpace_five_last ho S.original.head.paidRanks.lastActive
    (S.original.degree_six_terminal_mem ha ho) (S.original.head.head.coreInside hu)
  have aEq : a=-(P.eval 1) := by
    have atL := congrFun shape (Fin.last 18)
    have coord : lobattoTerminalAxis (K:=K) (Fin.last 18)=1 := by simp [lobattoTerminalAxis,coordinate]
    simp only [Pi.mul_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,evalNodes_apply,
      weightedEval_apply,S.headLast,uL,one,coord,mul_zero,add_zero,mul_one] at atL
    linear_combination -atL
  obtain ⟨s,hs,Q,qd,qe⟩ := S.mesh_repr ha ho
  refine ⟨P,R,Q,⟨S,pd,by omega,qd,p0,tests,⟨u,hu,?_⟩,⟨s,hs,qe⟩⟩⟩
  rw [shape,aEq,neg_smul,sub_eq_add_neg]

/-- The exact original-row product identity, keeping the physical
terminal correction in the linear line. -/
theorem LobattoSquareSection.transport (L : LobattoSquareSection A b U w v G P R Q) :
    weightedEval (nodes A) v (G-R*Q)-evalNodes A (P*Q)∈U⊔terminalMark A b := by
  obtain ⟨u,hu,square⟩ := L.square
  obtain ⟨s,hs,mesh⟩ := L.mesh
  have core := clock_function_mem
    (fun _ hx=>L.head.original.head.head.coreStable (Submodule.mem_map_of_mem hx)) Q.eval hu
  let x : Fin 19→K := fun i=>Q.eval (nodes A i)*u i
  have exactEq : weightedEval (nodes A) v (G-R*Q)-evalNodes A (P*Q)=
      x-(P.eval 1*(Q.eval (nodes A (Fin.last 18)))) • lobattoTerminalAxis := by
    funext i
    have g := congrFun mesh i
    have sq := congrFun square i
    simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.mul_apply,smul_eq_mul,evalNodes_apply,
      weightedEval_apply] at g sq
    have coreZero : s i*v i=0 := by
      by_cases z : s i=0
      · rw [z,zero_mul]
      · rw [L.head.clean _ ⟨s,hs,z⟩,mul_zero]
    have axisV : coordinate (K:=K) (Fin.last 18) i*v i=0 := by
      by_cases q : i=Fin.last 18
      · rw [q,L.head.headLast,mul_zero]
      · rw [coordinate_last_apply_zero q,zero_mul]
    have axisC : Q.eval (nodes A i)*coordinate (K:=K) (Fin.last 18) i=
        Q.eval (nodes A (Fin.last 18))*coordinate (K:=K) (Fin.last 18) i := by
      by_cases q : i=Fin.last 18
      · rw [q]
      · rw [coordinate_last_apply_zero q,mul_zero,mul_zero]
    simp only [lobattoTerminalAxis,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,weightedEval_apply,
      evalNodes_apply,eval_sub,eval_mul,x] at ⊢
    rw [g]
    linear_combination Q.eval (nodes A i)*sq+coreZero+
      (G.eval 1)*axisV-(P.eval 1)*axisC
  rw [exactEq]
  refine (U⊔terminalMark A b).sub_mem (Submodule.mem_sup_left core)
    (Submodule.mem_sup_right ?_)
  rw [terminalMark,if_pos L.head.original.seed]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem LobattoSquareSection.delta_cap (L : LobattoSquareSection A b U w v G P R Q) :
    (G-R*Q).natDegree≤8 :=
  (natDegree_sub_le _ _).trans (max_le (L.head.original.first.degree.le.trans (by decide))
    (natDegree_mul_le_of_le L.rd L.qd))

theorem natDegree_cap_of_zero_top {Z : K[X]} {n : ℕ} (cap : Z.natDegree≤n+1)
    (top : Z.coeff (n+1)=0) : Z.natDegree≤n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  by_cases e : i=n+1
  · rwa [e]
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem LobattoSquareSection.divides_of_low_delta (L : LobattoSquareSection A b U w v G P R Q)
    (low : (G-R*Q).coeff 8=0) : G∣P*Q := by
  let J := (P*Q)/G
  let T := (P*Q)%G
  have eq : G*J+T=P*Q := EuclideanDomain.div_add_mod (P*Q) G
  have gd : G.natDegree=6 := L.head.original.first.degree
  have gn : G≠0 := by intro z; rw [z,natDegree_zero] at gd; omega
  have dd := natDegree_cap_of_zero_top (n:=7) L.delta_cap low
  have td : T.natDegree≤5 := by
    have cap := natDegree_mod_lt (P*Q) (q:=G) (by omega)
    change T.natDegree<G.natDegree at cap
    omega
  have pd := natDegree_mul_le_of_le L.pd L.qd
  have pj : G*J=P*Q-T := eq_sub_of_add_eq eq
  have jd : J.natDegree≤2 := by
    have bound := (natDegree_sub_le (P*Q) T).trans (max_le pd (by omega : T.natDegree≤8))
    rw [←pj] at bound
    by_cases z : J=0
    · simp [z]
    · rw [natDegree_mul gn z,gd] at bound
      omega
  let B := markedEscapeHeadBand A b U v 8
  have wt : weightedEval (nodes A) v (G-R*Q)∈B :=
    Submodule.mem_sup_left (band_weighted_mem (by omega : (G-R*Q).natDegree<8))
  have inc : U⊔terminalMark A b≤B := sup_le_sup (band_core_le _) le_rfl
  have pq : evalNodes A (P*Q)∈B := by
    simpa only [sub_sub_cancel] using B.sub_mem wt (inc L.transport)
  have gmem : evalNodes A G∈markedEscapeHeadBand A b U v 4 := by
    rw [markedEscapeHeadBand,L.head.same _ (by decide)]
    exact first_alias_mem_markedEscapeHeadBand L.head.original.head L.head.original.first
  obtain ⟨d,hd,t,ht,gform⟩ := Submodule.mem_sup.mp gmem
  have gj : evalNodes A (G*J)∈B := by
    have headProd := ERK13OrdinarySquare.polynomial_times_band (n:=4) (d:=2) (by decide)
      L.head.original.head.head.coreStable hd J jd
    have line : evalNodes A J*t∈terminalMark A b := by
      rw [terminalMark,if_pos L.head.original.seed] at ht ⊢
      obtain ⟨s,rfl⟩ := Submodule.mem_span_singleton.mp ht
      refine Submodule.mem_span_singleton.mpr ⟨J.eval (nodes A (Fin.last 18))*s,?_⟩
      funext i
      by_cases e : i=Fin.last 18
      · rw [e]; simp only [Pi.smul_apply,smul_eq_mul,Pi.mul_apply,evalNodes_apply]; ring
      · simp only [Pi.smul_apply,smul_eq_mul,Pi.mul_apply,evalNodes_apply,coordinate_last_apply_zero e,
          mul_zero]
    have form : evalNodes A (G*J)=evalNodes A J*d+evalNodes A J*t := by
      have left : evalNodes A (G*J)=evalNodes A J*evalNodes A G := by
        funext i; simp only [evalNodes_apply,Pi.mul_apply,eval_mul,mul_comm]
      rw [left,←gform,mul_add]
    rw [form]
    exact Submodule.mem_sup.mpr ⟨_,escapeHeadBand_mono (by decide : 6≤8) headProd,_,line,rfl⟩
  have tJ : T=P*Q-G*J := by rw [←eq]; abel
  have tMem : evalNodes A T∈B := by rw [tJ,map_sub]; exact B.sub_mem pq gj
  have tMemOld : evalNodes A T∈markedEscapeHeadBand A b U w (2+2+4) := by
    change evalNodes A T∈escapeHeadBand A U w 8⊔terminalMark A b
    rw [←L.head.same _ (by decide)]
    exact tMem
  have tz := L.head.original.separated 4 (by decide) T td tMemOld
  exact ⟨J,by simpa only [tz,add_zero] using eq.symm⟩

theorem LobattoSquareSection.q_ne (L : LobattoSquareSection A b U w v G P R Q)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) : Q≠0 := by
  intro q0
  obtain ⟨u,hu,eq⟩ := L.mesh
  have many := L.head.more_physical_clocks ha ho
  let S := HeadFiber.physicalSites (nodes A) v
  have e : G=(0:K[X]) := by
    apply eq_of_degrees_lt_of_eval_finset_eq S
    · apply degree_le_natDegree.trans_lt
      exact_mod_cast (show G.natDegree<S.card by rw [L.head.original.first.degree]; exact Nat.lt_trans (by decide : 6<7) many)
    · simp
    · intro t ht
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
      have vi := (Finset.mem_filter.mp hi).2
      have ui : u i=0 := by
        by_contra nz
        exact vi (L.head.clean _ ⟨u,hu,nz⟩)
      have iL : i≠Fin.last 18 := fun h=>vi (h.symm ▸ L.head.headLast)
      have er := congrFun eq i
      simpa only [evalNodes_apply,Pi.add_apply,weightedEval_apply,Pi.smul_apply,smul_eq_mul,
        coordinate_last_apply_zero iL,q0,eval_zero,Pi.zero_apply,ui,zero_mul,mul_zero,zero_add,add_zero] using er
  have gd : G.natDegree=6 := L.head.original.first.degree
  rw [e,natDegree_zero] at gd
  omega

theorem LobattoSquareSection.impossible_of_low_delta (L : LobattoSquareSection A b U w v G P R Q)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (cut : LobattoPureFirstCut K) (low : (G-R*Q).coeff 8=0) : False := by
  obtain ⟨a,na,eq⟩ := L.head.original.degree_six_mesh_is_lobatto ha ho
  have normDiv : earlyLobattoMesh K∣G := ⟨C a,by rw [eq,smul_eq_C_mul,mul_comm]⟩
  have pz := lobatto_small_square_projection_zero L.pd L.p0 L.paid L.qd (L.q_ne ha ho)
    (normDiv.trans (L.divides_of_low_delta low))
  obtain ⟨u,hu,eqs⟩ := L.square
  have s8 : v*v∈zeroSpace A 8 := zeroSpace_mul L.head.headFour L.head.headFour
  have s6 : v*v∈escapeHeadBand A U v 6 := by
    rw [eqs,pz,map_zero,zero_add,eval_zero,zero_smul,sub_zero]
    exact (escapeHeadBand A U v 6).add_mem
      (band_weighted_mem (by have := L.rd; omega)) (band_core_le _ hu)
  have s5 : v*v∈escapeHeadBand A U v 5 := by
    rw [L.head.same _ (by decide)]
    rw [L.head.same _ (by decide)] at s6
    exact L.head.original.refund_one_head_slot ha ho (m:=2) (by decide) s8 s6
  obtain ⟨t,ht,T,td,form⟩ := band_polynomial_repr (by decide : 0<5) s5
  have amp (i : Fin 19) (nz : v i≠0) : v i=T.eval (nodes A i) := by
    have t0 : t i=0 := by
      by_contra nt
      exact nz (L.head.clean _ ⟨t,ht,nt⟩)
    have e := congrFun form i
    simp only [Pi.mul_apply,Pi.add_apply,weightedEval_apply,t0,zero_add] at e
    exact mul_right_cancel₀ nz e
  have many := L.head.more_physical_clocks ha ho
  have tn : T≠0 := by
    intro z
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0<(HeadFiber.physicalSites (nodes A) v).card by omega)
    obtain ⟨i,hi,_⟩ := Finset.mem_image.mp ha
    have nz := (Finset.mem_filter.mp hi).2
    exact nz (by rw [amp i nz,z,eval_zero])
  have gd : G.natDegree=6 := L.head.original.first.degree
  have dq := L.qd
  have fac := factor_of_clean_lobatto_sites (G:=G) (R:=T) (Q:=Q) (v:=v)
    (by omega) (by omega) L.head.headLast L.head.clean amp L.mesh
  exact L.head.impossible_of_factor ha ho cut (by omega) tn fac amp L.mesh

end
end RKResearch.Certified.Graded.ERK13NativeFirst
