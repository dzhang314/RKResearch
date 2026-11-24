module
public import RKCert.Dirk17EarlyBand
public import RKCert.Dirk17RadauQuadrature
public import RKCert.Dirk15EarlyScalars
@[expose] public section
namespace RKCert.Paired.Seventeen.Early
open Polynomial Module RKCert.OneEscape RKCert.Endpoint RKCert.RadauEight
open scoped Classical
noncomputable section
variable {K:Type*} [Field K] [CharZero K]
variable {A:Fin 23→Fin 23→K} {b:Vec K 23} {U:Submodule K (Vec K 23)} {w:Vec K 23} {n:ℕ}

omit [CharZero K] in
def evaluate (A:Fin 23→Fin 23→K) : K[X] →ₗ[K] Vec K 23:=
  LinearMap.pi (fun i=>leval (nodes A i))

omit [CharZero K] in
@[simp] theorem evaluate_eq (A:Fin 23→Fin 23→K) (P:K[X]) : evaluate A P=evalNodes A P:=rfl

omit [CharZero K] in
theorem evaluate_clock (P:K[X]):diag (nodes A) (evaluate A P)=evaluate A (X*P):=by
  ext i;simp only [evaluate_eq,diag_apply,evalNodes_apply,eval_mul,eval_X]

omit [CharZero K] in
def scalars (A:Fin 23→Fin 23→K):Submodule K (Vec K 23):=LinearMap.range (polyEval A 8)

omit [CharZero K] in
theorem scalars_rank (ho:HasTreeOrderAtLeast A b 17):finrank K (scalars A)=9:=by
  have inj:Function.Injective (polyEval A 8):=by
    intro a y e
    apply sub_eq_zero.mp
    apply poly_separated ho (by decide:2*8+1≤17)
    rw [map_sub,e,sub_self]
    exact Submodule.zero_mem _
  rw [scalars,LinearMap.finrank_range_of_inj inj,Module.finrank_fin_fun]

theorem pure_moment (ho:HasTreeOrderAtLeast A b 17) {P:K[X]} {m k:ℕ}
    (d:P.natDegree≤m) (v:evalNodes A P∈zeroSpace A m) (h:k+m+1≤17) :
    unitIntegral (P*X^k)=0:=by
  have z:probe A b k (evalNodes A P)=0:=probe_zeroSpace ho h v
  rw [(OrdinaryTrace.scalar A d).probe ho k h] at z
  simpa only [unitIntegral_apply,mul_comm P] using z

theorem origin_moments {d:ℕ} (P:K[X]) (dp:P.natDegree≤d+1) (org:P.eval 0=0)
    (obs:∀k≤d,unitIntegral (P*X^k)=0) : P=0:=by
  obtain ⟨H,e⟩:=X_dvd_iff.mpr (by simpa only [coeff_zero_eq_eval_zero] using org)
  by_cases hn:H=0
  · simp [e,hn]
  have h:=dp;rw [e,natDegree_X_mul hn] at h
  have hh:H=0:=primitive_shift_detect H (k:=1) (d:=d) (by omega) 1 one_ne_zero (fun j=>by
    have zap:=obs j.val (by have:=j.isLt;omega)
    rw [e,unitIntegral_apply,show X*H*X^j.val=X^(1+j.val)*H by rw [pow_add,pow_one];ring] at zap
    exact zap)
  simp [e,hh]

theorem grid_pure (R:Budget A) (ho:HasTreeOrderAtLeast A b 17) :
    evalNodes A (grid K)∈zeroSpace A 9:=by
  have mem:=evalNodes_mem_treeSpace A (grid K) (grid_degree (K:=K)).le
  rw [R.e9_full] at mem
  obtain ⟨_,⟨a,rfl⟩,f,hf,e⟩:=Submodule.mem_sup.mp mem
  let P:=ofFn 9 a
  have dP:P.natDegree≤8:=Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide:1≤9) a)
  have eq:evalNodes A P+f=evalNodes A (grid K):=by
    change evalNodes A (ofFn (8+1) a)+f=_
    rwa [evalNodes_ofFn]
  have zero:nodes A 0=0:=by simp [nodes,R.origin]
  have f0:f 0=0:=zeroSpace_first_of_row R.origin 9 hf
  have h0:P.eval 0=0:=by
    have e₀:=congrFun eq (0:Fin 23)
    change (evalNodes A P) 0+f 0=(evalNodes A (grid K)) 0 at e₀
    rw [evalNodes_apply,evalNodes_apply,zero,f0,add_zero,grid_native,zero_mul] at e₀
    exact e₀
  have pure:evalNodes A (grid K-P)∈zeroSpace A 9:=by
    have ee:evalNodes A (grid K-P)=f:=by
      change evaluate A (grid K-P)=f
      rw [map_sub,evaluate_eq,evaluate_eq,←eq,add_comm,add_sub_cancel_right]
    rwa [ee]
  have z:P=0:=origin_moments (d:=7) P dP h0 (fun k hk=>by
    have dd:(grid K-P).natDegree≤9:=(natDegree_sub_le _ _).trans (max_le (grid_degree (K:=K)).le (by omega))
    have zz:=pure_moment ho dd pure (k:=k) (by omega)
    have gv:unitIntegral (grid K*X^k)=0:=by
      have gg:=grid_orthogonal ((X:K[X])^k) (by rwa [natDegree_X_pow])
      simpa only [unitIntegral_apply,Terminal.integral_eq,formalPrimitive_eq_treePrimitive] using gg
    rw [sub_mul,map_sub,gv,zero_sub,neg_eq_zero] at zz
    exact zz)
  rw [z,show evalNodes A (0:K[X])=0 from by ext i;simp,zero_add] at eq
  exact eq ▸ hf

omit [CharZero K] in
theorem degree_reduction {P D:K[X]} {m:ℕ} (degD:D.natDegree=m+1) (degP:P.natDegree≤m+1) :
    ∃a:K,∃Q:K[X],Q.natDegree≤m ∧ P=Q+C a*D:=by
  have non:D.coeff (m+1)≠0:=by
    rw [←degD,coeff_natDegree]
    apply leadingCoeff_ne_zero.mpr
    intro e;rw [e,natDegree_zero] at degD;omega
  let a:=P.coeff (m+1)/D.coeff (m+1)
  let Q:=P-C a*D
  have wide:Q.natDegree≤m+1:=(natDegree_sub_le _ _).trans
    (max_le degP ((natDegree_C_mul_le _ _).trans degD.le))
  have z:Q.coeff (m+1)=0:=by simp only [Q,coeff_sub,coeff_C_mul,a,div_mul_cancel₀ _ non,sub_self]
  refine ⟨a,Q,natDegree_le_iff_coeff_eq_zero.mpr (fun i ih=>?_),by dsimp [Q];abel⟩
  by_cases e:i=m+1
  · rwa [e]
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

omit [CharZero K] in
def orb (A:Fin 23→Fin 23→K) (U:Submodule K (Vec K 23)) (w:Vec K 23) (n k:ℕ) :=
  chain (diag (nodes A)) U w (n+k)

omit [CharZero K] in
theorem orb_le {i j:ℕ} (h:i≤j) : orb A U w n i≤orb A U w n j:=by
  apply (chain_le_iff _).mpr
  obtain ⟨u,paid⟩:=((chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) (n+j)).mp le_rfl)
  exact ⟨u,fun k hk=>paid k (by omega)⟩

omit [CharZero K] in
theorem orb_step (h:Heads A U w n) (k:ℕ) :
    orb A U w n k ⊔ (orb A U w n k).map (diag (nodes A))=orb A U w n (k+1):=by
  change chain (diag (nodes A)) U w (n+k) ⊔ (chain (diag (nodes A)) U w (n+k)).map (diag (nodes A))=
    chain (diag (nodes A)) U w (n+(k+1))
  rw [chain_sup_map h.inv (by have:=h.len;omega),Nat.add_assoc]

structure Cut (A:Fin 23→Fin 23→K) (U:Submodule K (Vec K 23)) (w:Vec K 23) (n:ℕ):Prop where
  grid_paid : evalNodes A (grid K)∈zeroSpace A 9
  e10 : treeSpace A 10=scalars A⊔orb A U w n 4
  direct : Disjoint (scalars A) (orb A U w n 6)
  sites : n+5<(Clock.headSites (nodes A) w).card
  ten_head : orb A U w n 4≤zeroSpace A 10

theorem cut (R:Budget A) (h:Heads A U w n) (ho:HasTreeOrderAtLeast A b 17):Cut A U w n:=by
  classical
  let S:=scalars A
  let O:=orb A U w n
  let T:=diag (nodes A)
  have grid9:=grid_pure R ho
  have e9:treeSpace A 9=S⊔O 3:=by
    rw [R.e9_full,show zeroSpace A 9=O 3 from h.band 3 (by decide)]
    rfl
  have rise:S.map T≤S⊔O 3:=by
    rintro _ ⟨_,⟨a,rfl⟩,rfl⟩
    let H:=X*ofFn 9 a
    have d:(ofFn 9 a).natDegree≤8:=Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide:1≤9) a)
    have dH:H.natDegree≤9:=natDegree_mul_le.trans (by rw [natDegree_X];omega)
    obtain ⟨t,P,dP,e⟩:=degree_reduction (m:=8) (grid_degree (K:=K)) dH
    have eq:T (polyEval A 8 a)=evalNodes A P+t • evalNodes A (grid K):=by
      rw [←evalNodes_ofFn]
      change diag (nodes A) (evaluate A (ofFn 9 a))=_
      rw [evaluate_clock,show X*ofFn 9 a=H from rfl,e,←smul_eq_C_mul,map_add,map_smul]
      rfl
    rw [eq];apply (S⊔O 3).add_mem
    · apply (le_sup_left:S≤S⊔O 3)
      rw [evalNodes_eq_polyEval A _ dP]
      exact ⟨_,rfl⟩
    · apply (le_sup_right:O 3≤S⊔O 3)
      exact (O 3).smul_mem t ((h.band 3 (by decide)).le grid9)
  have step (k:ℕ)(hk:3≤k):((S⊔O k)⊔(S⊔O k).map T)=S⊔O (k+1):=by
    rw [Submodule.map_sup]
    have rs:S.map T≤S⊔O (k+1):=rise.trans (sup_le_sup_left (orb_le (by omega:3≤k+1)) _)
    apply le_antisymm
    · refine sup_le (sup_le_sup_left (orb_le (by omega:k≤k+1)) _) (sup_le rs ?_)
      exact (le_sup_right:(O k).map T≤O k⊔(O k).map T).trans ((orb_step h k).le.trans le_sup_right)
    · apply sup_le (le_sup_left.trans le_sup_left)
      change orb A U w n (k+1)≤_
      rw [←orb_step h k]
      exact sup_le (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_right)
  have e10:treeSpace A 10=S⊔O 4:=by
    rw [full_clock_step_of_unit (A:=A) (j:=9) (by
      have a:=R.e 9 (by decide) (by decide);have d:=R.e 10 (by decide) (by decide); 
      change finrank K (treeSpace A 10)≤finrank K (treeSpace A 9)+1;omega)
      (R.escapes 9 (by decide) (by decide)),e9]
    exact step 3 (by decide)
  have e11:treeSpace A 11=S⊔O 5:=by
    rw [full_clock_step_of_unit (A:=A) (j:=10) (by
      have a:=R.e 10 (by decide) (by decide);have d:=R.e 11 (by decide) (by decide);
      change finrank K (treeSpace A 11)≤finrank K (treeSpace A 10)+1;omega)
      (R.escapes 10 (by decide) (by decide)),e10]
    exact step 4 (by decide)
  have extend:treeSpace A 11⊔(treeSpace A 11).map T=S⊔O 6:=by rw [e11];exact step 5 (by decide)
  have strict:treeSpace A 11<S⊔O 6:=by
    rw [←extend]
    apply lt_of_le_of_ne le_sup_left
    intro eq
    exact R.escapes 11 (by decide) (by decide) (le_sup_right.trans eq.ge)
  have escape:¬(O 5).map T≤O 5:=by
    intro stay
    have u:(S⊔O 5).map T≤S⊔O 5:=by
      rw [Submodule.map_sup]
      exact sup_le (rise.trans (sup_le_sup_left (orb_le (by decide:3≤5)) _)) (stay.trans le_sup_right)
    exact R.escapes 11 (by decide) (by decide) (e11 ▸ u)
  have cap:finrank K (O 6)≤11:=by
    have a:=h.sum_rank
    have c:finrank K (O 6)≤finrank K U+(n+6):=chain_dim_upper _
    omega
  have sdim:finrank K S=9:=scalars_rank ho
  have rdim:=Submodule.finrank_sup_add_finrank_inf_eq S (O 6)
  have strictRank:=Submodule.finrank_lt_finrank_of_lt strict
  have last:=R.e 11 (by decide) (by decide)
  have inf0:finrank K (S⊓O 6 : Submodule K (Vec K 23))=0:=by omega
  have dis:Disjoint S (O 6):=by
    apply Submodule.disjoint_def.mpr
    intro x hx hy
    exact congrArg Subtype.val ((finrank_zero_iff_forall_zero.mp inf0) ⟨x,hx,hy⟩)
  have pu:O 4≤zeroSpace A 10:=by
    have base:O 3≤zeroSpace A 9:=(h.band 3 (by decide)).ge
    change orb A U w n (3+1)≤zeroSpace A 10
    rw [←orb_step h 3]
    exact sup_le (base.trans (zeroSpace_mono A (by decide:9≤10)))
      ((Submodule.map_mono base).trans (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A 9)))
  exact ⟨grid9,e10,dis,Clock.head_sites_of_noninvariant h.inv (by have:=h.len;omega) escape,pu⟩

theorem reduce_scalar (B:Cut A U w n) (h:Heads A U w n) (ho:HasTreeOrderAtLeast A b 17)
    {P:K[X]} (deg:P.natDegree≤9) (hp:evalNodes A P∈orb A U w n 6):
    ∃a:K,P=C a*grid K:=by
  classical
  obtain ⟨a,Q,dQ,e⟩:=degree_reduction (m:=8) (grid_degree (K:=K)) deg
  have v:evalNodes A (grid K)∈orb A U w n 6:=
    orb_le (by decide:3≤6) ((h.band 3 (by decide)).le B.grid_paid)
  have eq:evalNodes A Q=evalNodes A P-a • evalNodes A (grid K):=by
    change evaluate A Q=evaluate A P-a • evaluate A (grid K)
    rw [e,←smul_eq_C_mul,map_add,map_smul,add_sub_cancel_right]
  have s:evalNodes A Q∈scalars A:=by rw [evalNodes_eq_polyEval A _ dQ];exact ⟨_,rfl⟩
  have o:evalNodes A Q∈orb A U w n 6:=by rw [eq];exact Submodule.sub_mem _ hp (Submodule.smul_mem _ _ v)
  have nil:evalNodes A Q=0:=Submodule.disjoint_def.mp B.direct _ s o
  have cf:=poly_separated ho (by decide:2*8+1≤17) (fun j=>Q.coeff j.val) (by
    rw [←evalNodes_eq_polyEval A _ dQ,nil];exact Submodule.zero_mem _)
  have a0:Q=0:=by
    ext j
    rw [coeff_zero]
    by_cases l:j<9
    · exact congrFun cf ⟨j,l⟩
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  exact ⟨a,by rw [e,a0,zero_add]⟩

end
end RKCert.Paired.Seventeen.Early
