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

/-- No 20-stage-type substitute or full F10 chain is used here. True F5
squares are paid in F10, but their unwanted scalar component is removed
by the actual E10 clock comparison. The one-head branch only requires the
previously proved weighted fifth-debut theorem. -/
theorem no_five_four (R:Budget A) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17)
    (f5:finrank K (zeroSpace A 5)=4):False:=by
  let c:=nodes A
  let T:=diag c
  have n6:=R.f6
  have unit0:finrank K (zeroSpace A 6)≤finrank K (zeroSpace A 5)+1:=by omega
  have esc5:¬(zeroSpace A 5).map T≤zeroSpace A 5:=by
    intro inv
    have h:=dirk_forward_invariant_outgoing ha ho (j:=5) (by decide) (zeroSpace A 5) le_rfl
      (fun v hv=>inv ⟨v,hv,rfl⟩)
    change finrank K (zeroSpace A 5)+2≤finrank K (zeroSpace A 6) at h
    omega
  obtain ⟨r,U,w,pos,iv,uc,_,base,old_paid,_out,rank,norm,_sites⟩:=Clock.ordinary_normal_head A 5 unit0 esc5
  have caps (k:ℕ)(hk:k<4):finrank K (zeroSpace A (5+k+1))≤finrank K (zeroSpace A (5+k))+1:=by
    by_cases e:k=0
    · subst k;exact unit0
    have h:=units R (k-1) (by omega)
    rwa [show 6+(k-1)=5+k by omega] at h
  have esc (k:ℕ)(hk:k<4):¬(zeroSpace A (5+k)).map T≤zeroSpace A (5+k):=by
    by_cases e:k=0
    · subst k;exact esc5
    · exact ordinary_steps R ha ho (5+k) (by omega) (by omega)
  have flag:=Clock.ordinary_staircase iv pos base caps esc
  have big:2≤r:=by
    by_contra! small
    have er:r=1:=by omega
    subst r
    exact no_invariant_grade5_head ha ho (by decide) iv uc (fun k hk=>flag k (by omega))
  have h:Heads A U w (r+1):=by
    refine ⟨by omega,by omega,iv,uc.trans (zeroSpace_mono A (by decide)),norm,fun k hk=>?_⟩
    have e:=flag (k+1) (by omega)
    rwa [show 5+(k+1)=6+k by omega,show r+(k+1)=r+1+k by omega] at e
  have B:=cut R h ho
  have w5:w∈zeroSpace A 5:=by simpa only [pow_zero,one_apply_eq_self] using old_paid 0 pos
  have mul:Clock.MulClosed U:=fun _ ha' _ hb'=>core_absorbs R B h ho (by decide:5+5≤10) ha' uc (uc hb')
  obtain ⟨v,dif,dis,change_head⟩:=Clock.disjoint_head iv mul
    (fun u hu=>core_absorbs R B h ho (by decide:5+5≤10) hu uc w5)
  have normv (z:K) (u:Clock.fiber c z v∈U):Clock.fiber c z v=0:=by
    ext i
    change Clock.fiber c z v i=(0:K)
    by_cases eq:c i=z
    · have value:Clock.fiber c z v i=v i:=by simp [Clock.fiber,eq]
      rw [value]
      by_contra nz
      exact nz (dis i ⟨_,u,by rwa [value]⟩)
    · simp [Clock.fiber,eq]
  have basev:zeroSpace A 5=chain T U v r:=base.trans (change_head r).symm
  have h':Heads A U v (r+1):=
    ⟨h.len,h.sum_rank,h.inv,h.core,normv,fun k hk=>(h.band k hk).trans (change_head _).symm⟩
  have B':=cut R h' ho
  have cheap(k:ℕ)(hk:k<r):(T^k) v∈zeroSpace A 5:=((chain_le_iff r).mp basev.ge).2 _ hk
  have v5:v∈zeroSpace A 5:=by simpa only [pow_zero,one_apply_eq_self] using cheap 0 pos
  let d:=(r-1)+(r-1)
  have d1:1≤d:=by dsimp [d];omega
  let x(k:ℕ):Vec K 23:=(T^k) (v*v)
  have sq(k:ℕ)(hk:k≤d):x k∈zeroSpace A 10:=by
    let a:=min k (r-1)
    let q:=k-a
    have ap:a<r:=(Nat.min_le_right k (r-1)).trans_lt (by omega)
    have qp:q<r:=by dsimp [q,a,d] at *;omega
    have m:a+q=k:=by dsimp [a,q];exact Nat.add_sub_of_le (Nat.min_le_left _ _)
    have eq:x k=(T^a) v*(T^q) v:=by
      ext i;simp only [x,T,Clock.pow_diag_apply,Pi.mul_apply]
      rw [←m,pow_add];ring
    rw [eq]
    exact zeroSpace_mul (cheap a ap) (cheap q qp)
  have step(k:ℕ):T (x k)=x (k+1):=by
    change T ((T^k) (v*v))=(T^(k+1)) (v*v)
    rw [pow_succ',mul_apply_eq_comp]
  have inside(k:ℕ)(hk:k≤d):x k∈orb A U v (r+1) 4:=by
    by_cases lt:k<d
    · exact (strip_shift R B' h' ho (sq k hk) (sq (k+1) (by omega)) (step k)).1
    · have eq:(k-1)+1=k:=by omega
      have st:=step (k-1)
      rw [eq] at st
      exact (strip_shift R B' h' ho (sq (k-1) (by omega)) (sq k hk) st).2
  have cnt:(r+1)+4<(Clock.headSites c v).card:=by have:=B'.sites;exact (Nat.lt_succ_self _).trans this
  obtain ⟨P,ld,fit⟩:=Clock.multiplier_degree (U:=U) (a:=v) (n:=(r+1)+4) dis cnt inside
  have pn:P≠0:=by
    intro no
    obtain ⟨z,zs⟩:=Finset.card_pos.mp (by omega : 0<(Clock.headSites c v).card)
    obtain ⟨i,hi,_⟩:=Finset.mem_image.mp zs
    have vn:v i≠0:=(Finset.mem_filter.mp hi).2
    exact vn (by simpa only [no,eval_zero] using fit i vn)
  have deg:P.natDegree≤5:=by
    have s:=ld.resolve_left pn
    dsimp [d] at s
    omega
  obtain ⟨e,eu,ev⟩:=Clock.core_indicator mul
  let θ:=evalNodes A P-(weightedEval c e P+v)
  have ep:weightedEval c e P∈zeroSpace A 5:=uc (Clock.weightedEval_preserves iv P eu)
  have tr:OrdinaryTrace A 5 θ P:=(OrdinaryTrace.scalar A deg).sub_pure ((zeroSpace A 5).add_mem ep v5)
  apply clean_quintic_impossible R B' h' ha ho tr pn
  intro i act
  have off:¬Clock.Live U i:=by
    intro live
    apply act
    simp [θ,c,ev i,live,dis i live]
  have vz:v i=0:=by
    by_contra vn
    apply act
    simp [θ,c,ev i,off,fit i vn]
  intro f ff
  rw [show zeroSpace A 9=chain T U v ((r+1)+3) from h'.band 3 (by decide)] at ff
  obtain ⟨s,su,Q,_,rQ⟩:=Clock.exists_head_poly ff
  have sz:s i=0:=by
    by_contra nz
    exact off ⟨_,su,nz⟩
  rw [rQ i,sz,vz,mul_zero,add_zero]
end
end RKCert.Paired.Seventeen.Early
