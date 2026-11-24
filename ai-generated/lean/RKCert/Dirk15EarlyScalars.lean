module
public import RKCert.Dirk15EarlyBand
public import RKCert.Dirk15NonC2Orbit
@[expose] public section
namespace RKCert.Paired.EarlyFifteen
open Polynomial Module RKCert.OneEscape RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K:Type*} [Field K] [CharZero K]
variable {A:Fin 20→Fin 20→K} {b:Vec K 20} {U:Submodule K (Vec K 20)} {w:Vec K 20} {r:ℕ}

def relation (K:Type*) [Field K] : K[X] := X*radauLeft7

theorem relation_degree : (relation K).natDegree=8:=by
  have z:(radauLeft7:K[X]).coeff 7≠0:=by
    change (ofFn 8 (radauLeft7_coeff (K:=K))).coeff 7≠0
    rw [ofFn_coeff_eq_val_of_lt _ (by decide)]
    norm_num [radauLeft7_coeff]
  have d:=natDegree_eq_of_le_of_coeff_ne_zero radauLeft7_degree_le z
  have ne:(radauLeft7:K[X])≠0:=by intro e;rw [e,coeff_zero] at z;exact z rfl
  rw [relation,natDegree_mul X_ne_zero ne,natDegree_X,d]

theorem relation_test (Q:K[X]) (hq:Q.natDegree≤6) : unitIntegral (relation K*Q)=0:=by
  rw [relation,show X*radauLeft7*Q=(X*Q)*radauLeft7 by ring,unitIntegral_apply]
  rw [radauLeft7_reproduces _ (natDegree_mul_le.trans (by rw [natDegree_X];omega))]
  simp

theorem anchored_gram (H:K[X]) (dH:H.natDegree≤7) (z:H.eval 0=0)
    (test:∀ k≤6,unitIntegral (H*X^k)=0) : H=0:=by
  obtain ⟨P,e⟩:=X_dvd_iff.mpr (by simpa only [coeff_zero_eq_eval_zero] using z)
  by_cases pp:P=0
  · simp [e,pp]
  have q:=dH
  rw [e,natDegree_X_mul pp] at q
  have p0:P=0:=primitive_shift_detect P (k:=1) (d:=6) (by omega) 1 one_ne_zero (fun j=>by
    have eq:=test j.val (by have:=j.isLt;omega)
    rw [e,unitIntegral_apply,show X*P*X^j.val=X^(1+j.val)*P by rw [pow_add,pow_one];ring] at eq
    exact eq)
  simp [e,p0]

theorem relation_pure (B:Budget A) (ho:HasTreeOrderAtLeast A b 15) :
    evalNodes A (relation K)∈zeroSpace A 8:=by
  have mem:=evalNodes_mem_treeSpace A (relation K) (relation_degree (K:=K)).le
  rw [B.e8] at mem
  obtain ⟨_,⟨a,rfl⟩,v,hv,eq⟩:=Submodule.mem_sup.mp mem
  let H:=ofFn 8 a
  have dH:H.natDegree≤7:=Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide:1≤8) a)
  have e:evalNodes A H+v=evalNodes A (relation K):=by
    change evalNodes A (ofFn (7+1) a)+v=_
    rwa [evalNodes_ofFn]
  have n0:nodes A 0=0:=by simp [nodes,B.first]
  have v0:v 0=0:=zeroSpace_first_of_row B.first 8 hv
  have h0:H.eval 0=0:=by
    have aa:=congrFun e (0:Fin 20)
    change (evalNodes A H+v) 0=(evalNodes A (relation K)) 0 at aa
    simpa only [Pi.add_apply,evalNodes_apply,n0,v0,add_zero,relation,eval_mul,eval_X,zero_mul] using aa
  have pure:evalNodes A (relation K-H)∈zeroSpace A 8:=by
    have eqn:evalNodes A (relation K-H)=v:=by
      change evaluateColumn A (relation K-H)=v
      rw [map_sub,evaluateColumn_eq,evaluateColumn_eq,←e,add_comm,add_sub_cancel_right]
    rwa [eqn]
  have z:H=0:=anchored_gram H dH h0 (fun k hk=>by
    have dd:(relation K-H).natDegree≤8:=(natDegree_sub_le _ _).trans (max_le (relation_degree (K:=K)).le (by omega))
    have hh:=scalar_pure_unit_pair ho dd pure (Q:=X^k) (by rw [natDegree_X_pow];omega)
    rw [sub_mul,map_sub,relation_test _ (by rw [natDegree_X_pow];omega),zero_sub,neg_eq_zero] at hh
    exact hh)
  have eqz:evalNodes A (0:K[X])=0:=by ext i;simp
  rw [z,eqz,zero_add] at e
  exact e ▸ hv

theorem divide_eight {H:K[X]} (dH:H.natDegree≤8) :
    ∃ a:K,∃P:K[X],P.natDegree≤7 ∧ H=P+C a*relation K:=by
  let D:=relation K
  have dn:D.natDegree=8:=relation_degree
  have lead:D.coeff 8≠0:=by
    rw [←dn,coeff_natDegree]
    apply leadingCoeff_ne_zero.mpr
    intro e
    rw [e,natDegree_zero] at dn
    contradiction
  let a:=H.coeff 8/D.coeff 8
  let R:=H-C a*D
  have r8:R.natDegree≤8:=(natDegree_sub_le _ _).trans (max_le dH ((natDegree_C_mul_le _ _).trans dn.le))
  have c8:R.coeff 8=0:=by simp only [R,coeff_sub,coeff_C_mul,a,div_mul_cancel₀ _ lead,sub_self]
  refine ⟨a,R,natDegree_le_iff_coeff_eq_zero.mpr (fun k hk=>?_ ),by dsimp [R,D];abel⟩
  by_cases e:k=8
  · rwa [e]
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

omit [CharZero K] in
def orb (A:Fin 20→Fin 20→K) (U:Submodule K (Vec K 20)) (w:Vec K 20) (r k:ℕ) :=
  chain (diag (nodes A)) U w (r+k)

omit [CharZero K] in
theorem orb_le {i j:ℕ} (h:i≤j) : orb A U w r i≤orb A U w r j:=by
  apply (chain_le_iff _).mpr
  obtain ⟨u,paid⟩:=((chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) (r+j)).mp le_rfl)
  exact ⟨u,fun k hk=>paid k (by omega)⟩

omit [CharZero K] in
theorem orb_step (h:Heads A U w r) (k:ℕ) :
    orb A U w r k ⊔ (orb A U w r k).map (diag (nodes A))=orb A U w r (k+1):=by
  change chain (diag (nodes A)) U w (r+k) ⊔ (chain (diag (nodes A)) U w (r+k)).map (diag (nodes A))=chain (diag (nodes A)) U w (r+(k+1))
  rw [chain_sup_map h.inv (by have:=h.len;omega)]
  rw [Nat.add_assoc]

/-- An actual direct upper clock cut: no equality for E11 is asserted. -/
structure Cut (A:Fin 20→Fin 20→K) (U:Submodule K (Vec K 20)) (w:Vec K 20) (r:ℕ) : Prop where
  paid : evalNodes A (relation K)∈zeroSpace A 8
  e10 : treeSpace A 10=ordinaryScalarBand A ⊔orb A U w r 4
  direct : Disjoint (ordinaryScalarBand A) (orb A U w r 5)
  sites : r+4<(Clock.headSites (nodes A) w).card
  pure : orb A U w r 4≤zeroSpace A 10

theorem cut (B:Budget A) (h:Heads A U w r) (ho:HasTreeOrderAtLeast A b 15) : Cut A U w r:=by
  classical
  let S:=ordinaryScalarBand A
  let O:=orb A U w r
  let T:=diag (nodes A)
  have rel:=relation_pure B ho
  have e8:treeSpace A 8=S⊔O 2:=by
    have v:zeroSpace A 8=O 2:=h.band 2 (by decide)
    rw [B.e8,v]
    rfl
  have rise:S.map T≤S⊔O 2:=by
    rintro _ ⟨_,⟨a,rfl⟩,rfl⟩
    let H:=X*ofFn 8 a
    have d:(ofFn 8 a).natDegree≤7:=Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide:1≤8) a)
    have dH:H.natDegree≤8:=natDegree_mul_le.trans (by rw [natDegree_X];omega)
    obtain ⟨q,R,dR,eq⟩:=divide_eight dH
    have eqE:T (polyEval A 7 a)=evalNodes A R+q • evalNodes A (relation K):=by
      rw [←evalNodes_ofFn]
      change diag (nodes A) (evaluateColumn A (ofFn 8 a))=_
      rw [evaluateColumn_clock,show X*ofFn 8 a=H from rfl,eq,←smul_eq_C_mul,map_add,map_smul]
      rfl
    rw [eqE];apply (S⊔O 2).add_mem
    · apply (le_sup_left:S≤S⊔O 2)
      rw [evalNodes_eq_polyEval A _ dR]
      exact ⟨_,rfl⟩
    · apply (le_sup_right:O 2≤S⊔O 2)
      exact (O 2).smul_mem q ((h.band 2 (by decide)).le rel)
  have inc (k:ℕ)(hk:2≤k):((S⊔O k)⊔(S⊔O k).map T)=S⊔O (k+1):=by
    rw [Submodule.map_sup]
    have rs:S.map T≤S⊔O (k+1):=rise.trans (sup_le_sup_left (orb_le (by omega:2≤k+1)) _)
    apply le_antisymm
    · refine sup_le (sup_le_sup_left (orb_le (by omega:k≤k+1)) _) (sup_le rs ?_)
      exact (le_sup_right:(O k).map T≤O k⊔(O k).map T).trans ((orb_step h k).le.trans le_sup_right)
    · apply sup_le (le_sup_left.trans le_sup_left)
      change orb A U w r (k+1)≤_
      rw [←orb_step h k]
      exact sup_le (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_right)
  have e9:treeSpace A 9=S⊔O 3:=by
    have eq:=full_clock_step_of_unit (A:=A) (j:=8)
      (by have h₁:=B.e 8 (by decide) (by decide);have h₂:=B.e 9 (by decide) (by decide);
          change finrank K (treeSpace A 9)≤finrank K (treeSpace A 8)+1;omega)
      (B.escapes 8 (by decide) (by decide))
    rw [eq,e8];exact inc 2 (by decide)
  have e10:treeSpace A 10=S⊔O 4:=by
    have eq:=full_clock_step_of_unit (A:=A) (j:=9)
      (by have h₁:=B.e 9 (by decide) (by decide);have h₂:=B.e 10 (by decide) (by decide);
          change finrank K (treeSpace A 10)≤finrank K (treeSpace A 9)+1;omega)
      (B.escapes 9 (by decide) (by decide))
    rw [eq,e9];exact inc 3 (by decide)
  have e11:treeSpace A 10 ⊔ (treeSpace A 10).map T=S⊔O 5:=by rw [e10];exact inc 4 (by decide)
  have win:treeSpace A 10<S⊔O 5:=by
    rw [←e11]
    apply lt_of_le_of_ne le_sup_left
    intro e
    exact B.escapes 10 (by decide) (by decide) (le_sup_right.trans e.ge)
  have escape:¬(O 4).map T≤O 4:=by
    intro stay
    have im:(S⊔O 4).map T≤S⊔O 4:=by
      rw [Submodule.map_sup]
      exact sup_le (rise.trans (sup_le_sup_left (orb_le (by decide:2≤4)) _)) (stay.trans le_sup_right)
    exact B.escapes 10 (by decide) (by decide) (e10 ▸ im)
  have rkO:finrank K (O 5)≤10:=by
    have base:finrank K U+r=5:=h.rank_sum
    have cap:finrank K (O 5)≤finrank K U+(r+5):=chain_dim_upper _
    omega
  have rkS:finrank K S=8:=ordinaryScalarBand_rank ho
  have dim:=Submodule.finrank_lt_finrank_of_lt win
  have exact10:=B.e 10 (by decide) (by decide)
  have sdim:=Submodule.finrank_sup_add_finrank_inf_eq S (O 5)
  have zero:finrank K (S⊓O 5 : Submodule K (Vec K 20))=0:=by omega
  have dis:Disjoint S (O 5):=by
    apply Submodule.disjoint_def.mpr
    intro x hx hx'
    exact congrArg Subtype.val ((finrank_zero_iff_forall_zero.mp zero) ⟨x,hx,hx'⟩)
  have pu:O 4≤zeroSpace A 10:=by
    have base:O 2≤zeroSpace A 8:=(h.band 2 (by decide)).ge
    have later (k:ℕ) (ih:O k≤zeroSpace A (6+k)):O (k+1)≤zeroSpace A (6+k+1):=by
      change orb A U w r (k+1)≤zeroSpace A (6+k+1)
      rw [←orb_step h k]
      exact sup_le (ih.trans (zeroSpace_mono A (by omega)))
        ((Submodule.map_mono ih).trans (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A (6+k))))
    exact later 3 (later 2 base)
  exact ⟨rel,e10,dis,Clock.head_sites_of_noninvariant h.inv (by have:=h.len;omega) escape,pu⟩

theorem reduce_scalar (B:Cut A U w r) (h:Heads A U w r) (ho:HasTreeOrderAtLeast A b 15)
    {P:K[X]} (deg:P.natDegree≤8) (mem:evalNodes A P∈orb A U w r 5) :
    ∃ a:K,P=C a*relation K:=by
  classical
  obtain ⟨a,H,dh,e⟩:=divide_eight deg
  have dmem:evalNodes A (relation K)∈orb A U w r 5:=
    orb_le (by decide:2≤5) ((h.band 2 (by decide)).le B.paid)
  have HE:evalNodes A H=evalNodes A P-a • evalNodes A (relation K):=by
    change evaluateColumn A H=evaluateColumn A P-a • evaluateColumn A (relation K)
    rw [e,←smul_eq_C_mul,map_add,map_smul,add_sub_cancel_right]
  have HS:evalNodes A H∈ordinaryScalarBand A:=by rw [evalNodes_eq_polyEval A _ dh];exact ⟨_,rfl⟩
  have HP:evalNodes A H∈orb A U w r 5:=by
    rw [HE];exact Submodule.sub_mem _ mem (Submodule.smul_mem _ _ dmem)
  have Z:evalNodes A H=0:=Submodule.disjoint_def.mp B.direct _ HS HP
  have coeffs:=poly_separated ho (by decide:2*7+1≤15) (fun i=>H.coeff i.val) (by
    rw [←evalNodes_eq_polyEval A _ dh,Z];exact Submodule.zero_mem _)
  have hz:H=0:=by
    ext j
    rw [coeff_zero]
    by_cases lt:j<8
    · exact congrFun coeffs ⟨j,lt⟩
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  exact ⟨a,by rw [e,hz,zero_add]⟩
end
end RKCert.Paired.EarlyFifteen
