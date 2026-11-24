module

public import RKCert.Dirk15MinimalHiddenHead
public import RKCert.Dirk15DeletedPencilJacobi
public import RKCert.Dirk15PaidProductScalars
public import RKCert.Dirk15SquareSignature

@[expose] public section

/-! # Seventeen actual signatures after removing the original terminal and ghosts

The actual seventeen nonghost values derive a square identity from the
three paid grade-ten squares. This isolates the only free pencil norm,
without assuming a reduced RK tableau.
-/
namespace RKCert.Paired
open Module Polynomial RKCert.OneEscape RKCert.Endpoint
open Order15MinimalHead.DeletedPencil
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

omit [CharZero K] in
theorem deleteTerminal_eq_at_ne {v w : Vec K 20} (eq : deleteTerminal K 19 v=deleteTerminal K 19 w)
    (i : Fin 20) (ne : i≠Fin.last 19) : v i=w i := by
  revert ne
  refine Fin.lastCases (fun h => (h rfl).elim) (fun j _ => ?_) i
  exact congrFun eq j

namespace Order15HiddenHead
variable (h : Order15HiddenHead A b)

omit [CharZero K] in
theorem length_four : h.head.length=4 := by
  rw [Order15MinimalHead.length,h.core_two]

omit [CharZero K] in
theorem read_tail {u : Vec K 20} {n : ℕ} (pay : u∈chain (diag (nodes A)) h.head.U h.head.w n) :
    ∃ T : K[X], (T=0 ∨ T.natDegree<n) ∧
      ∀ i : Fin 20,i∉ghostPositions A b → u i=T.eval (nodes A i)*h.head.w i := by
  obtain ⟨v,hv,T,dT,e⟩ := Clock.exists_head_poly pay
  refine ⟨T,?_,fun i hi => ?_⟩
  · by_cases z : T=0
    · exact Or.inl z
    · exact Or.inr ((natDegree_lt_iff_degree_lt z).mpr dT)
  · have q := ghostPositions_vanish (h.core_eq ▸ hv) hi
    simpa only [q,zero_add] using e i

theorem unfolded_dirty_nodes (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b)
    (openHead : deleteTerminal K 19 (((diag (nodes A))^h.head.length) h.head.w)∉deletedTreeSpace A 7) :
    8≤(Clock.headSites (deleteTerminal K 19 (nodes A)) (deleteTerminal K 19 h.head.w)).card := by
  let U := h.head.U.map (deleteTerminal K 19)
  let w := deleteTerminal K 19 h.head.w
  let c := deleteTerminal K 19 (nodes A)
  let L := deletedHeadOrbit A h.head.U h.head.w (h.head.length+4)
  let S := deletedScalarOrbit A 7
  have form : deletedTreeSpace A 11=S⊔L := by
    rcases h.head.deleted_growth_dichotomy ha ho H with ⟨e,_⟩|⟨_,b⟩
    · exact (openHead e).elim
    · exact b 4 (by decide)
  have ed := (order15_minimal_deleted_band ha ho H 11 (by decide) (by decide)).2
  rw [form] at ed
  have hist := Submodule.finrank_sup_add_finrank_inf_eq S L
  rw [ed] at hist
  have scalar : finrank K S≤8 := Order15MinimalHead.deleted_scalar_rank_upper 7
  have core : finrank K U≤2 := (Submodule.finrank_map_le _ _).trans h.core_two.le
  have tail : finrank K L≤finrank K U+(Clock.headSites c w).card :=
    chain_dim_sites (c:=c) (w:=w) (U:=U) _
  change 8≤(Clock.headSites c w).card
  omega

variable (D : h.head.DeletedPencil)

structure NativeSquareSignatures where
  R : K[X]
  T : K[X]
  V : K[X]
  scale : K
  Rdegree : R.natDegree≤4
  Tdegree : T.natDegree≤4
  Vdegree : V.natDegree≤8
  relation : ∀ i : Fin 20,i≠Fin.last 19 → i∉ghostPositions A b →
    D.D.eval (nodes A i)=h.head.w i*R.eval (nodes A i)
  square : ∀ i : Fin 20,i≠Fin.last 19 → i∉ghostPositions A b →
    (h.head.w i)^2=h.head.w i*T.eval (nodes A i)+scale*V.eval (nodes A i)
  branch :
    (V=X*jacobiTwo K 7 ∧ ∃ a : K,a≠0 ∧ D.D=C a*(X*jacobiTwo K 6)) ∨
    (V=X*jacobiTwo K 6 ∧ ∃ a t : K,a≠0 ∧ D.D=C a*(X*(jacobiTwo K 7+C t*jacobiTwo K 6)))

omit [CharZero K] in
private theorem degree_drop_clock {P Q R : K[X]} {d : ℕ}
    (pos : 0<d) (q : Q.natDegree≤d) (r : R.natDegree≤d) (eq : Q=X*P-R) :
    P.natDegree≤d-1 := by
  by_contra! fail
  have pn : P≠0 := by intro e; rw [e,natDegree_zero] at fail; omega
  have pd : (X*P).natDegree=1+P.natDegree := by rw [natDegree_mul X_ne_zero pn,natDegree_X]
  rw [eq,natDegree_sub_eq_left_of_natDegree_lt (by omega),pd] at q
  omega

set_option maxHeartbeats 2100000 in
theorem actual_square_signatures (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b) : Nonempty (h.NativeSquareSignatures D) := by
  obtain ⟨u,hu,R,dr,relation⟩ := D.head_profile
  have hd : R.natDegree≤4 := h.length_four ▸ dr
  let c := nodes A
  let w := h.head.w
  have rd (i : Fin 20) (hi : i≠Fin.last 19) (hg : i∉ghostPositions A b) :
      D.D.eval (c i)=w i*R.eval (c i) := by
    have e := relation i hi
    have ui : u i=0 := ghostPositions_vanish (v:=u) (h.core_eq ▸ hu) hg
    rw [ui,zero_add,mul_comm] at e
    exact e
  have pay (i : Fin 3) : originalClockShift A (w*w) i.val∈zeroSpace A 10 := h.square_paid i
  rcases D.jacobi_shape with ⟨folded,a,an,aD⟩ | ⟨unfolded,a,t,an,aD⟩
  · obtain ⟨S⟩ := D.folded_paid_shifts ha ho H folded pay
    obtain ⟨sigma,δ,s0⟩ := S.folded_initial_three (by simpa [folded] using D.growth)
    obtain ⟨T,dd,Trep⟩ := h.read_tail (S.paid 0)
    have dT : T.natDegree≤3 := by
      rcases dd with e|e
      · simp [e]
      · rw [h.length_four] at e
        omega
    let W := X*jacobiTwo K 7
    let P := T+C (δ/a)*R
    have Wd : W.natDegree≤8 := natDegree_mul_le.trans (by norm_num [natDegree_X,jacobiTwo_degree])
    have Pd : P.natDegree≤4 := (natDegree_add_le _ _).trans
      (max_le (dT.trans (by decide)) ((natDegree_C_mul_le _ _).trans hd))
    have newS : S.poly 0=C sigma*W+C (δ/a)*D.D := by
      rw [s0,aD]
      have cprod : C (δ/a)*C a=C δ := by rw [←map_mul,div_mul_cancel₀ _ an]
      change X*(C sigma*jacobiTwo K 7+C δ*jacobiTwo K 6)=
        C sigma*(X*jacobiTwo K 7)+C (δ/a)*(C a*(X*jacobiTwo K 6))
      rw [show C (δ/a)*(C a*(X*jacobiTwo K 6))=(C (δ/a)*C a)*(X*jacobiTwo K 6) by ac_rfl,cprod]
      ring
    refine ⟨⟨R,P,W,sigma,hd,Pd,Wd,rd,?_,Or.inl ⟨rfl,a,an,aD⟩⟩⟩
    intro i ni gi
    have eq := deleteTerminal_eq_at_ne (S.decomposition 0) i ni
    change w i*w i=(S.poly 0).eval (c i)+S.tail 0 i at eq
    have e : (S.poly 0).eval (c i)=sigma*W.eval (c i)+(δ/a)*D.D.eval (c i) := by
      simp only [newS,eval_add,eval_mul,eval_C]
    rw [e,rd i ni gi,Trep i gi] at eq
    change w i^2=w i*(T+C (δ/a)*R).eval (c i)+sigma*W.eval (c i)
    rw [eval_add,eval_mul,eval_C]
    linear_combination eq
  · obtain ⟨S⟩ := D.unfolded_paid_shifts ha ho H unfolded pay
    obtain ⟨sigma,s0⟩ := S.unfolded_initial_three
    let W := X*jacobiTwo K 6
    have Wd : W.natDegree≤8 := natDegree_mul_le.trans (by norm_num [natDegree_X,jacobiTwo_degree])
    have parts (i : Fin 3) := h.read_tail (S.paid i)
    choose T dT repr using parts
    have td (i : Fin 3) : (T i).natDegree≤6 := by
      rcases dT i with e|e
      · simp [e]
      · rw [h.length_four] at e
        omega
    have next (i : Fin 2) : ∃ k : K,T i.succ=X*T i.castSucc-C k*R := by
      obtain ⟨k,eq⟩ := S.adjacent i
      refine ⟨k,?_⟩
      let c' := deleteTerminal K 19 c
      let w' := deleteTerminal K 19 w
      let Z := Clock.headSites c' w'
      have z8 : 8≤Z.card := h.unfolded_dirty_nodes ha ho H unfolded
      apply Polynomial.eq_of_degrees_lt_of_eval_finset_eq Z
      · exact degree_le_natDegree.trans_lt (by exact_mod_cast
          ((td i.succ).trans_lt (by omega : 6<Z.card)))
      · have dd : (X*T i.castSucc-C k*R).natDegree≤7 := (natDegree_sub_le _ _).trans
          (max_le (natDegree_mul_le.trans (by rw [natDegree_X]; have := td i.castSucc; omega))
            ((natDegree_C_mul_le _ _).trans (hd.trans (by decide))))
        exact degree_le_natDegree.trans_lt (by exact_mod_cast (dd.trans_lt (by omega : 7<Z.card)))
      · intro z zi
        obtain ⟨j,jm,rfl⟩ := Finset.mem_image.mp zi
        let p := j.castSucc
        have wp : w p≠0 := (Finset.mem_filter.mp jm).2
        have gn : p∉ghostPositions A b := fun e => wp (h.head_zero p e)
        have nt : p≠Fin.last 19 := Fin.castSucc_ne_last j
        have v₁ := deleteTerminal_eq_at_ne (S.decomposition i.succ) p nt
        have v₀ := deleteTerminal_eq_at_ne (S.decomposition i.castSucc) p nt
        change ((diag c)^i.succ.val) (w*w) p=(S.poly i.succ).eval (c p)+S.tail i.succ p at v₁
        change ((diag c)^i.castSucc.val) (w*w) p=(S.poly i.castSucc).eval (c p)+S.tail i.castSucc p at v₀
        rw [Clock.pow_diag_apply,repr i.succ p gn] at v₁
        rw [Clock.pow_diag_apply,repr i.castSucc p gn] at v₀
        have e := congrArg (eval (c p)) eq
        rw [eval_add,eval_mul,eval_X,eval_mul,eval_C,rd p nt gn] at e
        change (T i.succ).eval (c p)=(X*T i.castSucc-C k*R).eval (c p)
        rw [eval_sub,eval_mul,eval_X,eval_mul,eval_C]
        apply mul_right_cancel₀ wp
        change c p^(i.val+1)*(w*w) p=_ at v₁
        change c p^i.val*(w*w) p=_ at v₀
        rw [pow_succ'] at v₁
        linear_combination c p*v₀-v₁-e
    obtain ⟨k,step⟩ := next 0
    obtain ⟨q,step'⟩ := next 1
    change T 1=X*T 0-C k*R at step
    change T 2=X*T 1-C q*R at step'
    have d1 : (T 1).natDegree≤5 := degree_drop_clock (by decide : 0<6) (td 2)
      ((natDegree_C_mul_le _ _).trans (hd.trans (by decide))) step'
    have d0 : (T 0).natDegree≤4 := degree_drop_clock (by decide : 0<5) d1
      ((natDegree_C_mul_le _ _).trans (hd.trans (by decide))) step
    refine ⟨⟨R,T 0,W,sigma,hd,d0,Wd,rd,?_,Or.inr ⟨rfl,a,t,an,aD⟩⟩⟩
    intro i it ig
    have eq := deleteTerminal_eq_at_ne (S.decomposition 0) i it
    change w i*w i=(S.poly 0).eval (c i)+S.tail 0 i at eq
    rw [s0,eval_mul,eval_C,repr 0 i ig] at eq
    change w i^2=w i*(T 0).eval (c i)+sigma*W.eval (c i)
    linear_combination eq

theorem NativeSquareSignatures.exact_identity (S : h.NativeSquareSignatures D)
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15) (H : Order15MinimalMarkedChart A b) :
    Signature.squareSignatureExpression D.D S.R S.T S.V S.scale=0 := by
  obtain ⟨idx,_,ret,_,inj,_⟩ := h.seventeen_signatures ha ho H
  exact Signature.square_signatures_close (fun i => nodes A (idx i)) (fun i => h.head.w (idx i))
    D.D S.R S.T S.V S.scale
    ((Signature.square_signature_degree_bound D.dmax S.Rdegree S.Tdegree S.Vdegree).trans_lt (by decide))
    inj (fun i => S.relation _ (ret i).1 (ret i).2) (fun i => S.square _ (ret i).1 (ret i).2)

end Order15HiddenHead
end
end RKCert.Paired
