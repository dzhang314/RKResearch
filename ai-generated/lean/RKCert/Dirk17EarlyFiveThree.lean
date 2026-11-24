module
public import RKCert.Dirk17EarlyPivots
public import RKCert.DirkOneFiberCut
@[expose] public section
namespace RKCert.Paired.Seventeen.Early
open Module Polynomial RKCert.OneEscape RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K:Type*} [Field K] [CharZero K]
variable {A:Fin 23→Fin 23→K} {b:Vec K 23}
variable {V U:Submodule K (Vec K 23)} {g w:Vec K 23} {r n:ℕ}

structure SmallBand (A:Fin 23→Fin 23→K) (V U:Submodule K (Vec K 23)) (g:Vec K 23) (r:ℕ):Prop where
  pos:0<r
  inv:V.map (diag (nodes A))≤V
  inside:V≤U
  paid:V≤zeroSpace A 4
  four:zeroSpace A 4=chain (diag (nodes A)) V g r
  extra:chain (diag (nodes A)) V g (r+2)≤zeroSpace A 6
  outside:g∉U
  count:finrank K V+r=2

theorem small_bands (R:Budget A) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17)
    (f5:finrank K (zeroSpace A 5)=3):
    ∃V U g w r n,SmallBand A V U g r ∧ Heads A U w n:=by
  let T:=diag (nodes A)
  have f4:=R.f4
  have f7:=R.f7
  have out4:¬(zeroSpace A 4).map T≤zeroSpace A 4:=by
    intro inv
    have e:=dirk_forward_invariant_outgoing ha ho (j:=4) (by decide) (zeroSpace A 4)
      le_rfl (fun _ hv=>inv ⟨_,hv,rfl⟩)
    change finrank K (zeroSpace A 4)+2≤finrank K (zeroSpace A 5) at e
    omega
  have out5:¬(zeroSpace A 5).map T≤zeroSpace A 5:=by
    intro inv
    have e:=dirk_forward_invariant_incoming ha ho (j:=5) (by decide) (fun _ hv=>inv ⟨_,hv,rfl⟩)
    change finrank K (zeroSpace A 4)+2≤finrank K (zeroSpace A 5) at e
    omega
  obtain ⟨U,w,n,H,maximal⟩:=heads R ha ho
  obtain ⟨r,V,g,pos,iv,vc,_max4,four,_cheap,_e,rank,_norm,_s⟩:=
    Clock.ordinary_normal_head A 4 (by change finrank K (zeroSpace A 5)≤finrank K (zeroSpace A 4)+1;omega) out4
  have vi:V≤U:=maximal V iv (vc.trans (zeroSpace_mono A (by decide)))
  have five:zeroSpace A 5=chain T V g (r+1):=by
    rw [Clock.ordinary_step (A:=A) (j:=4) (by change finrank K (zeroSpace A 5)≤finrank K (zeroSpace A 4)+1;omega) out4,
      four,chain_sup_map iv pos]
  have gOut:g∉U:=by
    intro inside
    have sub:zeroSpace A 5≤U:=five.le.trans ((chain_le_iff _).mpr ⟨vi,fun k _=>pow_mem H.inv inside k⟩)
    have q:=dirk_forward_invariant_outgoing ha ho (j:=6) (by decide) U H.core (fun _ hv=>H.inv ⟨_,hv,rfl⟩)
    change finrank K U+3≤finrank K (zeroSpace A 7) at q
    have eq:zeroSpace A 5=U:=Submodule.eq_of_le_of_finrank_le sub (by omega)
    apply out5
    rw [eq]
    exact H.inv
  have extra:chain T V g (r+2)≤zeroSpace A 6:=by
    rw [show r+2=(r+1)+1 by omega,←chain_sup_map iv (by omega),←five]
    exact sup_le (zeroSpace_mono A (by decide)) (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A 5))
  exact ⟨V,U,g,w,r,n,⟨pos,iv,vi,vc,four,extra,gOut,by omega⟩,H⟩

omit [CharZero K] in
theorem small_narrow (S:SmallBand A V U g r) (H:Heads A U w n) (B:Cut A U w n):
    ∃u∈U,∃L:K[X],L≠0 ∧ L.natDegree+(finrank K U-finrank K V)≤1 ∧
      ∀i,g i=u i+L.eval (nodes A i)*w i:=by
  have hh:zeroSpace A 6=chain (diag (nodes A)) U w n:=H.band 0 (by decide)
  have powers(k:ℕ)(hk:k≤r+1):(diag (nodes A)^k) g∈chain (diag (nodes A)) U w n:=
    hh.le (((chain_le_iff _).mp S.extra).2 _ (by omega))
  obtain ⟨u,hu,L,shape,rep⟩:=Clock.overlapping_head_degree H.inv H.normal (by have:=B.sites;omega) powers
  have ln:L≠0:=by
    intro e
    have eq:g=u:=by ext i;simpa only [e,eval_zero,zero_mul,add_zero] using rep i
    exact S.outside (eq ▸ hu)
  have de:=shape.resolve_left ln
  have sums:=H.sum_rank
  have sumv:=S.count
  have ineq:=Submodule.finrank_mono S.inside
  exact ⟨u,hu,L,ln,by omega,rep⟩

omit [CharZero K] in
theorem small_squares (S:SmallBand A V U g r) (H:Heads A U w n):
    ∀k≤(r-1)+(r-1),(diag (nodes A)^k) (g*g)∈chain (diag (nodes A)) U w (n+2):=by
  let T:=diag (nodes A)
  have p:=S.pos
  have all4:=((chain_le_iff (T:=T) (U:=V) (w:=g) r).mp S.four.ge).2
  have endb:zeroSpace A 8=chain T U w (n+2):=H.band 2 (by decide)
  intro k kg
  let a:=min k (r-1)
  let q:=k-a
  have ia:a<r:=(Nat.min_le_right k (r-1)).trans_lt (by omega)
  have iq:q<r:=by dsimp [q,a];omega
  have e:a+q=k:=by dsimp [q,a];exact Nat.add_sub_of_le (Nat.min_le_left _ _)
  have z:(T^k) (g*g)=(T^a) g*(T^q) g:=by
    ext i;simp only [T,Clock.pow_diag_apply,Pi.mul_apply];rw [←e,pow_add];ring
  rw [←endb,z]
  exact zeroSpace_mul (all4 _ ia) (all4 _ iq)

theorem small_dirty_quintic (J:Budget A) (S:SmallBand A V U g r) (H:Heads A U w n)
    (D:Cut A U w n) (ho:HasTreeOrderAtLeast A b 17):
    ∃(P:K[X]) (θ:Vec K 23),P≠0 ∧ OrdinaryTrace A 5 θ P ∧
      ∀i,θ i≠0→Clean A i:=by
  classical
  let c:=nodes A
  have rp:=S.pos
  have pos:=H.len
  have us:=D.sites
  have dim:=Submodule.finrank_mono S.inside
  have eqdim:=(show finrank K U+n=finrank K V+r+3 by have a:=S.count;have b:=H.sum_rank;omega)
  obtain ⟨u,uu,L,ln,ld,ef⟩:=small_narrow S H D
  obtain ⟨d,du,Q,qd,sq⟩:=Clock.overlapping_head_degree H.inv H.normal (by omega) (small_squares S H)
  obtain ⟨cut⟩:=Clock.core_cut_of_codimension S.inside S.inv H.inv (by omega)
  let B:=cut.B
  have bn:B≠0:=cut.nz
  have bd:B.natDegree≤finrank K U-finrank K V:=cut.deg
  let R:=B*L
  have rn:R≠0:=mul_ne_zero bn ln
  have dr:R.natDegree≤1:=by
    have q:=natDegree_mul_le (p:=B) (q:=L); dsimp only [R];omega
  have first:zeroSpace A 4=chain (diag c) V g r:=by simpa [c] using S.four
  have later:zeroSpace A 6=chain (diag c) U w n:=by simpa [c] using H.band 0 (by decide)
  have last:zeroSpace A 9=chain (diag c) U w (n+3):=H.band 3 le_rfl
  have g4:g∈zeroSpace A 4:=by
    have e:=((chain_le_iff _).mp first.ge).2 0 rp
    simpa using e
  have w6:w∈zeroSpace A 6:=by
    have e:=((chain_le_iff _).mp later.ge).2 0 pos
    simpa using e
  have good:cut.good≤zeroSpace A 4:=cut.inside.trans S.paid
  have mixed {x y:Vec K 23} (hx:x∈cut.good) (hy:y∈zeroSpace A 6):x*y∈cut.good:=by
    apply cut.keep x hx y
    rw [←Clock.sum_fibers (nodes A) x,Finset.sum_mul]
    apply Submodule.sum_mem
    intro a _
    have inF:Clock.fiber (nodes A) a x∈zeroSpace A 4:=good (Clock.fiber_mem cut.inv a hx)
    exact local_ten J D H ho (a:=a) (zeroSpace_mul inF hy) (fun i ne=>by simp [Clock.fiber,ne])
  have up:zeroSpace A 4≤zeroSpace A 6:=zeroSpace_mono A (by decide)
  have alg:Clock.MulClosed cut.good:=fun _ hx _ hy=>mixed hx (up (good hy))
  obtain ⟨e,eg,ie⟩:=Clock.core_indicator alg
  have ew:=mixed eg w6
  have noCore (i:Fin 23) (off:¬Clock.Live cut.good i) (hit:B.eval (c i)≠0) (a:Vec K 23) (ha:a∈U):a i=0:=by
    have z:weightedEval c a B i=0:=by
      by_contra ne
      exact off ⟨_,cut.clear a ha,ne⟩
    exact (mul_eq_zero.mp (by simpa only [weightedEval_apply] using z)).resolve_left hit
  have qn:Q≠0:=by
    intro zero
    have mem:weightedEval c w R∈U:=by
      have ewr:weightedEval c w R=weightedEval c (e*w) R:=by
        ext i
        by_cases live:Clock.Live cut.good i
        · simp [ie,live]
        by_cases hit:B.eval (c i)=0
        · simp [R,hit]
        have gg:g i=0:=by
          have ss:=sq i
          simp only [Pi.mul_apply,noCore i live hit d du,zero,eval_zero,zero_mul,add_zero] at ss
          exact (mul_self_eq_zero.mp ss)
        have z:L.eval (c i)*w i=0:=by simpa only [gg,noCore i live hit u uu,zero_add] using (ef i).symm
        simp only [weightedEval_apply,Pi.mul_apply,ie,ite_eq_right live,zero_mul,mul_zero,R,eval_mul]
        rw [mul_assoc,z,mul_zero]
      rw [ewr];exact S.inside (cut.inside (Clock.weightedEval_preserves cut.inv R ew))
    have de:R.degree<((Clock.headSites c w).card:WithBot ℕ):=by
      apply (natDegree_lt_iff_degree_lt rn).mp;change R.natDegree<(Clock.headSites (nodes A) w).card;omega
    exact rn (eq_zero_of_degree_lt_of_eval_finset_eq_zero _ de
      (Clock.scalar_head_vanishes H.inv H.normal mem))
  let P:=B*Q
  have pn:P≠0:=mul_ne_zero bn qn
  have degree:P.natDegree≤5:=by
    have short:=qd.resolve_left qn
    have mult:=natDegree_mul_le (p:=B) (q:=Q);dsimp only [P];omega
  let v:=g-e*g
  have v4:v∈zeroSpace A 4:=(zeroSpace A 4).sub_mem g4 (good (mixed eg (up g4)))
  have pay:weightedEval c v R∈zeroSpace A 5:=by
    have e0:weightedEval c v R=v*evalNodes A R:=by ext i;simp [c,mul_comm]
    rw [e0]
    exact zeroSpace_mono A (by omega:4+R.natDegree≤5)
      (zeroSpace_mul_treeSpace ho (by omega) v4 (evalNodes_mem_treeSpace A R le_rfl))
  let z:=weightedEval c e P+weightedEval c v R
  have z5:z∈zeroSpace A 5:=(zeroSpace A 5).add_mem
    (zeroSpace_mono A (by decide:4≤5) (good (Clock.weightedEval_preserves cut.inv P eg))) pay
  let θ:=evalNodes A P-z
  refine ⟨P,θ,pn,(OrdinaryTrace.scalar A degree).sub_pure z5,?_⟩
  intro i active f hf
  have live:¬Clock.Live cut.good i:=by
    intro on
    apply active
    simp [θ,z,v,ie,on,c]
  by_cases hit:B.eval (c i)=0
  · exfalso
    apply active
    simp only [θ,z,Pi.sub_apply,Pi.add_apply,evalNodes_apply,weightedEval_apply,P,R,eval_mul]; change B.eval (c i)*Q.eval (c i)-(B.eval (c i)*Q.eval (c i)*e i+(B.eval (c i)*L.eval (c i))*v i)=0;rw [hit];ring
  have match_g:g i=L.eval (c i)*w i:=by simpa only [noCore i live hit u uu,zero_add] using ef i
  have off:w i=0:=by
    by_contra nz
    have ss:=sq i
    simp only [Pi.mul_apply,noCore i live hit d du,zero_add] at ss
    have prod:(L.eval (c i)*g i)*w i=Q.eval (c i)*w i:=by
      calc
        _=g i*(L.eval (c i)*w i):=by ring
        _=g i*g i:=by rw [←match_g]
        _=_:=ss
    have val:=mul_right_cancel₀ nz prod
    apply active
    simp only [θ,z,v,evalNodes_apply,Pi.sub_apply,Pi.add_apply,Pi.mul_apply,weightedEval_apply,ie,ite_eq_right live,zero_mul,sub_zero,mul_zero,zero_add,P,R,eval_mul]
    change B.eval (c i)*Q.eval (c i)-(B.eval (c i)*L.eval (c i))*g i=0
    rw [←val];ring
  rw [last] at hf
  obtain ⟨a,ha,_,_,eqn⟩:=Clock.exists_head_poly hf
  rw [eqn i,noCore i live hit a ha,off,mul_zero,add_zero]


theorem no_five_three (R:Budget A) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17)
    (f5:finrank K (zeroSpace A 5)=3):False:=by
  obtain ⟨V,U,g,w,r,n,S,H⟩:=small_bands R ha ho f5
  have B:=cut R H ho
  obtain ⟨P,θ,pn,tr,clean⟩:=small_dirty_quintic R S H B ho
  exact clean_quintic_impossible R B H ha ho tr pn clean
end
end RKCert.Paired.Seventeen.Early
