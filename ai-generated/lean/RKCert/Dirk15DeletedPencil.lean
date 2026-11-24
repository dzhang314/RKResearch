module

public import RKCert.Dirk15MinimalDeletedHead

@[expose] public section

/-! # Genuine polynomial relation across the physical terminal

The missing physical value remains a free multiple of the terminal
cardinal. It is eliminated from every paid moment by the true factor
1-X, never by an assumption of zero there.
-/
namespace RKCert.Paired
open Module Polynomial RKCert.OneEscape RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

omit [CharZero K] in
theorem terminal_cardinal_not_pure (ho : HasTreeOrderAtLeast A b 15)
    (hb : b (Fin.last 19)≠0) (j : ℕ) (pay : j+1≤15) :
    terminalCardinal K 19∉zeroSpace A j := by
  intro h
  have e : probe A b 0 (terminalCardinal K 19)=0 :=
    probe_zeroSpace ho (by omega : 0+j+1≤15) h
  change row (fun i => b i*(nodes A i)^0) (Pi.single (Fin.last 19) 1)=0 at e
  rw [row_single_right] at e
  exact hb (by simpa using e)

omit [CharZero K] in
theorem deleted_pure_same (ho : HasTreeOrderAtLeast A b 15)
    (hb : b (Fin.last 19)≠0) {j : ℕ} (pay : j+1≤15) {u v : Vec K 20}
    (hu : u∈zeroSpace A j) (hv : v∈zeroSpace A j)
    (e : deleteTerminal K 19 u=deleteTerminal K 19 v) : u=v := by
  have t := deleteTerminal_inj_on (terminal_cardinal_not_pure ho hb j pay) (a₁:=⟨u,hu⟩) (a₂:=⟨v,hv⟩) e
  exact congrArg Subtype.val t

theorem deleted_scalar_pure_tests (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b) {j : ℕ} {P : K[X]} {v : Vec K 20}
    (dP : P.natDegree≤j) (hv : v∈zeroSpace A j)
    (rel : deleteTerminal K 19 (evalNodes A P)=deleteTerminal K 19 v) :
    P.eval 0=0 ∧ ∀ Q : K[X], j+Q.natDegree+2≤15 →
      unitIntegral (P*((1-X)*Q))=0 := by
  have c0 : nodes A 0=0 := by simp [nodes,H.initial.first_zero]
  have first := congrFun rel (0:Fin 19)
  change P.eval (nodes A 0)=v 0 at first
  rw [c0,show v 0=0 from zeroSpace_first_of_row H.initial.first_zero j hv] at first
  refine ⟨first,fun Q hQ => ?_⟩
  let R := (1-X)*Q
  have dR : j+R.natDegree+1≤15 := by
    have e : R.natDegree≤1+Q.natDegree := natDegree_mul_le.trans (by rw [one_sub_clock_degree])
    omega
  have trace : OrdinaryTrace A j v 0 := by
    refine ⟨by simp,?_⟩
    have z : evalNodes A (0:K[X])=0 := by ext i; simp
    simpa only [z,sub_zero] using hv
  have e := (OrdinaryTrace.scalar A dP).pair_polynomial ho R dR
  have ep := trace.pair_polynomial ho R dR
  have v0 : row (weightedEval (nodes A) b R) v=0 := by
    simpa [formalPrimitive] using ep
  have diff : deleteTerminal K 19 (evalNodes A P-v)=0 := by rw [map_sub,rel,sub_self]
  have lift := (deleteTerminal_zero_iff _).mp diff
  let α := (evalNodes A P-v) (Fin.last 19)
  have rwzero : row (weightedEval (nodes A) b R) (terminalCardinal K 19)=0 := by
    change row (weightedEval (nodes A) b R) (Pi.single (Fin.last 19) 1)=0
    rw [row_single_right,weightedEval_apply,H.terminal.node_one]
    simp [R]
  have final : row (weightedEval (nodes A) b R) (evalNodes A P)=0 := by
    have t := congrArg (row (weightedEval (nodes A) b R)) lift
    rw [map_sub,v0,sub_zero,map_smul,rwzero,smul_zero] at t
    exact t
  rw [final] at e
  exact e.symm

theorem deleted_paid_pencil_degree (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b) {P : K[X]} {v : Vec K 20}
    (dP : P.natDegree≤8) (hv : v∈zeroSpace A 8) (pn : P≠0)
    (rel : deleteTerminal K 19 (evalNodes A P)=deleteTerminal K 19 v) :
    7≤P.natDegree := by
  have t := deleted_scalar_pure_tests ho H dP hv rel
  have dz : X∣P := by
    have eq : X-C (0:K)∣P := dvd_iff_isRoot.mpr t.1
    simpa only [map_zero,sub_zero] using eq
  obtain ⟨Q,e⟩ := dz
  by_contra! h
  have qn : Q≠0 := fun eq => pn (by rw [e,eq,mul_zero])
  rw [e,natDegree_mul X_ne_zero qn,natDegree_X] at h
  apply qn
  apply two_end_weight_primitive_detect Q (d:=5) (k:=1) (by omega)
  intro i
  have hm := t.2 (X^i.val) (by rw [natDegree_X_pow]; have := i.isLt; omega)
  change unitIntegral (P*((1-X)*X^i.val))=0 at hm
  rw [e,show X*Q*((1-X)*X^i.val)=X^(1+i.val)*((1-X)*Q) by rw [pow_add,pow_one]; ring] at hm
  exact hm

namespace Order15MinimalHead
variable (h : Order15MinimalHead A b)

structure DeletedPencil where
  D : K[X]
  v : Vec K 20
  dmin : 7≤D.natDegree
  dmax : D.natDegree≤8
  genuine : v∈chain (diag (nodes A)) h.U h.w (h.length+1)
  eq : deleteTerminal K 19 (evalNodes A D)=deleteTerminal K 19 v
  origin : D.eval 0=0
  quiet : ∀ Q : K[X], Q.natDegree≤5 → unitIntegral (D*((1-X)*Q))=0
  growth : if deleteTerminal K 19 (((diag (nodes A))^h.length) h.w)∈deletedTreeSpace A 7
    then D.natDegree=7 else D.natDegree=8

set_option maxHeartbeats 1600000 in
theorem deleted_pencil (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b) : Nonempty h.DeletedPencil := by
  classical
  let d := deleteTerminal K 19
  let C' := diag (nodes A)
  let L := chain C' h.U h.w
  let a := (C'^h.length) h.w
  have aL : a∈L (h.length+1) := by
    change a∈L h.length⊔K∙a
    exact (le_sup_right : (K∙a)≤_) (Submodule.subset_span rfl)
  have phase : ∃ P : K[X], ∃ v∈L (h.length+1), P≠0 ∧ P.natDegree≤8 ∧
      d (evalNodes A P)=d v ∧
      (if d a∈deletedTreeSpace A 7 then P.natDegree≤7 else P.natDegree=8) := by
    rcases h.deleted_growth_dichotomy ha ho H with ⟨folded,_⟩ | ⟨unfolded,band⟩
    · have fold : d a∈deletedTreeSpace A 7 := folded
      rw [h.deleted_base ho,deletedHeadOrbit_eq] at folded
      obtain ⟨q,hq,z,hz,eq⟩ := Submodule.mem_sup.mp folded
      obtain ⟨P,pd,rfl⟩ := deletedScalarOrbit_decompose hq
      obtain ⟨y,hy,rfl⟩ := hz
      have rel : d (evalNodes A P)=d (a-y) := by
        rw [map_sub,←eq,add_sub_cancel_right]
      have ay : a-y∈L (h.length+1) :=
        (L (h.length+1)).sub_mem aL ((clock_chain_mono (Nat.le_succ _)) hy)
      have pn : P≠0 := by
        intro pz
        have f : a-y∈zeroSpace A 8 := h.length_next_pure ay
        have e : d (a-y)=d 0 := by
          rw [←rel,pz]
          congr 1
          ext i
          simp
        have eq0 := deleted_pure_same ho H.terminal.weight_ne (by decide) f
          ((zeroSpace A 8).zero_mem) e
        have et : a=y := sub_eq_zero.mp eq0
        have escaped : a∉zeroSpace A 7 := h.length_next_unpaid
        apply escaped
        rw [et]
        rw [show zeroSpace A 7=L h.length from h.seven]
        exact hy
      exact ⟨P,a-y,ay,pn,pd.trans (by decide),rel,by simpa [fold] using pd⟩
    · have pow8 : d (evalNodes A (X^8:K[X]))∈deletedTreeSpace A 8 := by
        apply Submodule.mem_map_of_mem
        rw [evalNodes_eq_polyEval A _ (by rw [natDegree_X_pow])]
        exact polyEval_mem_treeSpace _ _ _
      have bd : deletedTreeSpace A 8=deletedScalarOrbit A 7⊔deletedHeadOrbit A h.U h.w (h.length+1) :=
        band 1 (by decide)
      rw [bd,deletedHeadOrbit_eq] at pow8
      obtain ⟨q,hq,z,hz,eq⟩ := Submodule.mem_sup.mp pow8
      obtain ⟨Q,qd,rfl⟩ := deletedScalarOrbit_decompose hq
      obtain ⟨v,hv,rfl⟩ := hz
      let P : K[X] := X^8-Q
      have degree8 : P.natDegree=8 := by
        change (X^8-Q).natDegree=8
        rw [natDegree_sub_eq_left_of_natDegree_lt (by rw [natDegree_X_pow]; omega),natDegree_X_pow]
      have pn : P≠0 := fun z => by rw [z,natDegree_zero] at degree8; contradiction
      have e : d (evalNodes A P)=d v := by
        change d (evaluateColumn A (X^8-Q))=d v
        rw [map_sub,map_sub,evaluateColumn_eq,evaluateColumn_eq,←eq,add_sub_cancel_left]
      have notIn : ¬ d a∈deletedTreeSpace A 7 := unfolded
      exact ⟨P,v,hv,pn,degree8.le,e,by simpa [notIn] using degree8⟩
  obtain ⟨P,v,vL,pn,pd,e,ch⟩ := phase
  have v8 : v∈zeroSpace A 8 := h.length_next_pure vL
  have target := deleted_scalar_pure_tests ho H pd v8 e
  have low := deleted_paid_pencil_degree ho H pd v8 pn e
  refine ⟨⟨P,v,low,pd,vL,e,target.1,(fun Q dq => target.2 Q (by omega)),?_⟩⟩
  by_cases f : d a∈deletedTreeSpace A 7
  · change (if d a∈deletedTreeSpace A 7 then P.natDegree=7 else P.natDegree=8)
    simp only [f,ite_true] at ch ⊢
    omega
  · change (if d a∈deletedTreeSpace A 7 then P.natDegree=7 else P.natDegree=8)
    simpa [f] using ch

end Order15MinimalHead
end
end RKCert.Paired
