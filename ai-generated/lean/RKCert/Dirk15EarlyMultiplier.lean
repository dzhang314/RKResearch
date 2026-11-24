module
public import RKCert.Dirk15EarlyPure
public import RKCert.Dirk15EarlyProjectedPivot
@[expose] public section
namespace RKCert.Paired.EarlyFifteen
open Polynomial Module RKCert.OneEscape RKCert.Endpoint PivotProjection
open scoped Classical
noncomputable section
variable {K:Type*} [Field K] [CharZero K]
variable {A:Fin 20→Fin 20→K} {b:Vec K 20} {U:Submodule K (Vec K 20)} {w v:Vec K 20} {r:ℕ}
variable {π:ClockRetraction (nodes A) U}

omit [CharZero K] in
theorem projected_head {n:ℕ} {f:Vec K 20} (m:f∈chain (diag (nodes A)) U w n) :
    ∃P:K[X],P.degree<(n:WithBot ℕ) ∧
      π.projection f=weightedEval (nodes A) (π.projection w) P:=by
  obtain ⟨u,hu,P,dP,e⟩:=Clock.exists_head_poly m
  have eq:f=u+weightedEval (nodes A) w P:=by ext i;simpa only [Pi.add_apply,weightedEval_apply] using e i
  exact ⟨P,dP,by rw [eq,map_add,π.kills _ hu,zero_add,π.weighted]⟩

theorem projected_multiplier (R:Budget A) (B:Cut A U w r) (h:Heads A U w r)
    (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 15)
    (comm:∀x,π.projection (diag v x)=diag v (π.projection x))
    (v6:v∈zeroSpace A 6) (cv:diag (nodes A) v∈zeroSpace A 5)
    {n:ℕ} (lo:2≤n) (enough:r+3≤n+4) (pay:∀ k≤n,v*((diag (nodes A)^k) w)∈zeroSpace A 10) :
    v∈U:=by
  let D:=diag (nodes A)
  let x (k:ℕ):Vec K 20:=v*((D^k) w)
  let W:=π.projection w
  have step (k:ℕ) (_:k<n) : D (x k)=x (k+1):=by
    ext i
    simp only [D,x,diag_apply,Pi.mul_apply,Clock.pow_diag_apply]
    rw [pow_succ (nodes A i) k]
    ring
  have orbit:=strip_ladder R B h ho x lo pay step
  have repr (k:Fin (n+1)) : ∃P:K[X],P.degree<((r+4:ℕ):WithBot ℕ) ∧
      π.projection (x k.val)=weightedEval (nodes A) W P:=
    projected_head (orbit k.val (by have:=k.isLt;omega))
  choose Q deg fit using repr
  have nat (k:Fin (n+1)):(Q k).natDegree≤r+3:=by
    by_cases z:Q k=0
    · simp [z]
    have bound: (Q k).natDegree<r+4:=(natDegree_lt_iff_degree_lt z).mpr (deg k)
    omega
  have value (k:Fin (n+1)) (i:Fin 20) (act:W i≠0) :
      (Q k).eval (nodes A i)=v i*nodes A i^k.val:=by
    have e:=congrFun (fit k) i
    change π.projection (diag v ((D^k.val) w)) i=weightedEval (nodes A) W (Q k) i at e
    rw [comm,π.clock_pow,diag_apply,Clock.pow_diag_apply,weightedEval_apply] at e
    apply mul_right_cancel₀ act
    rw [←e]
    ring
  have many:r+4<(Clock.headSites (nodes A) W).card:=B.sites.trans_le
    (Finset.card_le_card (π.head_sites w h.normal))
  have head_step (k:Fin n):Q k.succ=X*Q k.castSucc:=by
    have dd:(Q k.succ-X*Q k.castSucc).natDegree≤r+4:=(natDegree_sub_le _ _).trans
      (max_le ((nat _).trans (by omega)) (natDegree_mul_le.trans (by rw [natDegree_X];have:=nat k.castSucc;omega)))
    have e:Q k.succ-X*Q k.castSucc=0:=by
      by_contra ne
      have bd:(Q k.succ-X*Q k.castSucc).degree<((Clock.headSites (nodes A) W).card:WithBot ℕ):=
        (natDegree_lt_iff_degree_lt ne).mp (dd.trans_lt many)
      apply ne (eq_zero_of_degree_lt_of_eval_finset_eq_zero _ bd ?_)
      intro u hu
      obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hu
      have act:W i≠0:=(Finset.mem_filter.mp hi).2
      rw [eval_sub,eval_mul,eval_X,value k.succ i act,value k.castSucc i act,Fin.val_succ,Fin.val_castSucc,pow_succ]
      ring
    exact sub_eq_zero.mp e
  have mul (a:ℕ) (al:a≤n):Q ⟨a,by omega⟩=X^a*Q 0:=by
    induction a with
    | zero => simp
    | succ a ih =>
      let k:Fin n:=⟨a,by omega⟩
      change Q k.succ=X^(a+1)*Q 0
      rw [head_step k,show Q k.castSucc=X^a*Q 0 from ih (by omega),pow_succ',mul_assoc]
  have pol: (Q 0).natDegree≤4:=by
    by_cases nz:Q 0=0
    · simp [nz]
    have bd:=nat ⟨n,by omega⟩
    rw [mul n le_rfl,natDegree_mul (pow_ne_zero _ X_ne_zero) nz,natDegree_pow,natDegree_X,mul_one] at bd
    omega
  have fit0 (i:Fin 20)(act:W i≠0):v i=(Q 0).eval (nodes A i):=by
    symm
    simpa only [Fin.val_zero,pow_zero,mul_one] using value 0 i act
  have allv (i:Fin 20):π.projection v i=v i*(π.projection 1) i:=by
    have e:diag v (1:Vec K 20)=v:=by ext j;simp
    exact congrFun (e ▸ comm (1:Vec K 20)) i
  have eq6:zeroSpace A 6=chain D U w r:=h.band 0 (by decide)
  obtain ⟨G,_,offv⟩:=projected_head (π:=π) (eq6.le v6)
  have off (i:Fin 20)(wn:W i=0):π.projection v i=0:=by
    rw [offv,weightedEval_apply]
    change G.eval (nodes A i)*W i=0
    rw [wn,mul_zero]
  let z:=evalNodes A (X*Q 0)-D v
  have tr:OrdinaryTrace A 5 z (X*Q 0):=
    (OrdinaryTrace.scalar A (natDegree_mul_le.trans (by rw [natDegree_X];omega))).sub_pure cv
  have q0:Q 0=0:=by
    apply projected_quartic_zero (P:=π) ha ho h.core B.paid (Q 0) pol tr
    intro i active
    have form:π.projection z i=nodes A i*((Q 0).eval (nodes A i)*(π.projection 1) i-π.projection v i):=by
      simp only [z,map_sub,Pi.sub_apply,projected_eval,eval_mul,eval_X,D,π.clock,diag_apply]
      ring
    have w0:W i=0:=by
      by_contra wn
      apply active
      rw [form,allv,fit0 i wn,sub_self,mul_zero]
    have eq:π.projection z i=nodes A i*((Q 0).eval (nodes A i)*(π.projection 1) i):=by
      rw [form,off i w0,sub_zero]
    have nz:=mul_ne_zero_iff.mp (eq ▸ active)
    exact ⟨(mul_ne_zero_iff.mp nz.2).2,nz.1,fun f ff=>projected_clean (P:=π) h w0 f ff⟩
  have pv:π.projection v=0:=by
    ext i
    by_cases wn:W i=0
    · exact off i wn
    · rw [allv,fit0 i wn,q0,eval_zero,zero_mul,Pi.zero_apply]
  simpa only [pv,sub_zero] using π.defect v

theorem diagonal_product_invariant (R:Budget A) (B:Cut A U w r) (h:Heads A U w r)
    (ho:HasTreeOrderAtLeast A b 15) {j k:ℕ} (paid:j+k≤10) (uv:U≤zeroSpace A k)
    (hv:v∈zeroSpace A j) : U.map (diag v)≤U:=by
  rintro _ ⟨u,uu,rfl⟩
  have e:diag v u=v*u:=by ext i;rfl
  rw [e,←Clock.sum_fibers (nodes A) u,Finset.mul_sum]
  apply Submodule.sum_mem
  intro a _
  have uf:=Clock.fiber_mem h.inv a uu
  have tor:v*Clock.fiber (nodes A) a u∈zeroSpace A 10:=
    zeroSpace_mono A paid (zeroSpace_mul (A:=A) (m:=j) (n:=k) hv (uv uf))
  exact localized_ten R B h ho (a:=a) tor (fun i hi=>by simp [Clock.fiber,hi])

theorem grade_four_in_core (R:Budget A) (B:Cut A U w r) (h:Heads A U w r)
    (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 15) : zeroSpace A 4≤U:=by
  intro v hv
  have inv:=diagonal_product_invariant R B h ho (by decide:4+6≤10) h.core hv
  have infK : Infinite K := Infinite.of_injective (fun n:ℕ=>(n:K)) Nat.cast_injective
  obtain ⟨π,hh⟩:=@exists_joint_retraction K _ 20 infK (nodes A) v U h.inv inv
  have f6:zeroSpace A 6=chain (diag (nodes A)) U w r:=h.band 0 (by decide)
  have cheap (k:ℕ) (kk:k≤r-1): (diag (nodes A)^k) w∈zeroSpace A 6:=
     f6.ge (((chain_le_iff r).mp (le_rfl:chain (diag (nodes A)) U w r≤_)).2 k (by have:=h.len;omega))
  have n2:2≤r-1:=by have:=h.len;omega
  have eq:r+3≤(r-1)+4:=by have:=h.len;omega
  exact projected_multiplier R B h ha ho hh (zeroSpace_mono A (by decide:4≤6) hv)
    (diag_zeroSpace A 4 hv) n2 eq (fun k kk=>zeroSpace_mul (A:=A) (m:=4) (n:=6) hv (cheap k kk))

end
end RKCert.Paired.EarlyFifteen
