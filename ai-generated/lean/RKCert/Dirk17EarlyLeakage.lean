module
public import RKCert.Dirk17LeakagePolynomial
@[expose] public section
namespace RKCert.Paired.Seventeen.Early
open Polynomial Module RKCert.OneEscape RKCert.Endpoint RKCert.RadauEight
open scoped Classical
noncomputable section
variable {K:Type*} [Field K] [CharZero K]
variable {A:Fin 23→Fin 23→K} {b:Vec K 23} {U:Submodule K (Vec K 23)} {w:Vec K 23} {n:ℕ}

/-- At true grade ten the only extra scalar direction is X times the
left Radau reproducer from grade seven. The head terms are genuinely pure. -/
theorem ten_parts (R:Budget A) (B:Cut A U w n) (ho:HasTreeOrderAtLeast A b 17)
    {x:Vec K 23} (hx:x∈zeroSpace A 10) :
    ∃a:K,∃y∈orb A U w n 4,x=evalNodes A (C a*EarlyFifteen.relation K)+y:=by
  have mem:=zeroSpace_le_treeSpace A 10 hx
  rw [B.e10] at mem
  obtain ⟨_,⟨a,rfl⟩,y,hy,eq⟩:=Submodule.mem_sup.mp mem
  let H:=ofFn 9 a
  have dH:H.natDegree≤8:=Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide:1≤9) a)
  have e:x=evalNodes A H+y:=by
    change x=evalNodes A (ofFn (8+1) a)+y
    rw [evalNodes_ofFn];exact eq.symm
  have pure:evalNodes A H∈zeroSpace A 10:=by
    rw [show evalNodes A H=x-y by rw [e];abel]
    exact Submodule.sub_mem _ hx (B.ten_head hy)
  have n0:nodes A 0=0:=by simp [nodes,R.origin]
  have h0:H.eval 0=0:=by
    have j:evalNodes A H 0=0:=zeroSpace_first_of_row R.origin 10 pure
    rwa [evalNodes_apply,n0] at j
  obtain ⟨c,P,dP,h⟩:=EarlyFifteen.divide_eight dH
  have p0:P.eval 0=0:=by
    rwa [h,eval_add,eval_mul,eval_C,EarlyFifteen.relation,eval_mul,eval_X,zero_mul,mul_zero,add_zero] at h0
  have zero:P=0:=origin_moments (d:=6) P dP p0 (fun k hk=>by
    have out:=pure_moment ho (dH.trans (by decide)) pure (k:=k) (by omega)
    rw [h,add_mul,map_add,show C c*EarlyFifteen.relation K*X^k=c • (EarlyFifteen.relation K*X^k) by
      rw [smul_eq_C_mul];ring,map_smul,EarlyFifteen.relation_test _ (by rwa [natDegree_X_pow]),smul_zero,add_zero] at out
    exact out)
  exact ⟨c,y,hy,by rwa [h,zero,zero_add] at e⟩

/-- Two adjacent genuine grade-ten pure vectors cannot carry any of the
wrong scalar direction: the fixed degree-nine correction and its two
neighbors are linearly independent. -/
theorem strip_shift (R:Budget A) (B:Cut A U w n) (h:Heads A U w n)
    (ho:HasTreeOrderAtLeast A b 17) {x y:Vec K 23}
    (xp:x∈zeroSpace A 10) (yp:y∈zeroSpace A 10) (same:diag (nodes A) x=y):
    x∈orb A U w n 4 ∧ y∈orb A U w n 4:=by
  obtain ⟨a,v,hv,xv⟩:=ten_parts R B ho xp
  obtain ⟨d,z,hz,yz⟩:=ten_parts R B ho yp
  let L:=EarlyFifteen.relation K
  have vv:evalNodes A (X*(C a*L)-C d*L)=z-diag (nodes A) v:=by
    change evaluate A (X*(C a*L)-C d*L)=_
    rw [map_sub,←evaluate_clock,evaluate_eq,evaluate_eq]
    rw [xv,yz,map_add] at same
    change diag (nodes A) (evalNodes A (C a*L))-evalNodes A (C d*L)=_
    change diag (nodes A) (evalNodes A (C a*L))+diag (nodes A) v=evalNodes A (C d*L)+z at same
    linear_combination same
  have inside:evalNodes A (X*(C a*L)-C d*L)∈orb A U w n 6:=by
    rw [vv]
    apply Submodule.sub_mem _ (orb_le (by decide:4≤6) hz)
    apply orb_le (by decide:5≤6)
    exact (orb_step h 4).le ((le_sup_right:(orb A U w n 4).map (diag (nodes A))≤_)
      (Submodule.mem_map_of_mem hv))
  have dg:L.natDegree=8:=EarlyFifteen.relation_degree
  have da:(C a*L).natDegree≤8:=(natDegree_C_mul_le _ _).trans dg.le
  have dd:(C d*L).natDegree≤8:=(natDegree_C_mul_le _ _).trans dg.le
  have deg:(X*(C a*L)-C d*L).natDegree≤9:=(natDegree_sub_le _ _).trans
    (max_le (natDegree_mul_le.trans (by rw [natDegree_X];omega)) (by omega))
  obtain ⟨c,e⟩:=reduce_scalar B h ho deg inside
  obtain ⟨az,dz⟩:=leakage_shift_independent a d c e
  have xx:x=v:=by
    rw [xv,az,map_zero,zero_mul,show evalNodes A (0:K[X])=0 from by ext i;simp,zero_add]
  have yy:y=z:=by
    rw [yz,dz,map_zero,zero_mul,show evalNodes A (0:K[X])=0 from by ext i;simp,zero_add]
  exact ⟨xx ▸ hv,yy ▸ hz⟩

theorem local_ten (R:Budget A) (B:Cut A U w n) (h:Heads A U w n)
    (ho:HasTreeOrderAtLeast A b 17) {x:Vec K 23} (xp:x∈zeroSpace A 10) {a:K}
    (loc:∀i,nodes A i≠a→x i=0):x∈U:=by
  have same:diag (nodes A) x=a • x:=by
    ext i
    by_cases e:nodes A i=a
    · simp [e]
    · simp [loc i e]
  have hh:=strip_shift R B h ho xp ((zeroSpace A 10).smul_mem a xp) same
  exact Clock.localized_mem h.inv h.normal (by have:=B.sites;omega) hh.1 loc

theorem core_absorbs (R:Budget A) (B:Cut A U w n) (h:Heads A U w n)
    (ho:HasTreeOrderAtLeast A b 17) {j k:ℕ} (pay:j+k≤10)
    {u v:Vec K 23} (hu:u∈U) (uf:U≤zeroSpace A j) (hv:v∈zeroSpace A k):
    u*v∈U:=by
  rw [←Clock.sum_fibers (nodes A) u,Finset.sum_mul]
  apply Submodule.sum_mem
  intro a _
  have ufib:=Clock.fiber_mem h.inv a hu
  apply local_ten R B h ho (a:=a) (zeroSpace_mono A pay (zeroSpace_mul (uf ufib) hv))
  intro i ne
  simp [Clock.fiber,ne]

def Clean (A:Fin 23→Fin 23→K) (i:Fin 23):Prop:=∀f∈zeroSpace A 9,f i=0

omit [CharZero K] in
theorem clean_orb (h:Heads A U w n) {i:Fin 23} (hc:Clean A i)
    {m:ℕ} {f:Vec K 23} (hf:f∈orb A U w n m):f i=0:=by
  change f∈chain (diag (nodes A)) U w (n+m) at hf
  have w₆:w∈zeroSpace A 6:=
    (show zeroSpace A 6=chain (diag (nodes A)) U w n from h.band 0 (by decide)).ge
      (by simpa only [pow_zero,one_apply_eq_self] using
        ((chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) n).mp le_rfl).2 0 h.len)
  have wi:=hc _ (zeroSpace_mono A (by decide:6≤9) w₆)
  obtain ⟨z,zu,P,_,eq⟩:=Clock.exists_head_poly hf
  rw [eq i,wi,hc _ (zeroSpace_mono A (by decide:6≤9) (h.core zu)),mul_zero,zero_add]

theorem ten_clean_trace (R:Budget A) (B:Cut A U w n) (h:Heads A U w n)
    (ho:HasTreeOrderAtLeast A b 17) {f:Vec K 23} (hf:f∈zeroSpace A 10):
    ∃a:K,∀i,Clean A i→f i=a*(EarlyFifteen.relation K).eval (nodes A i):=by
  obtain ⟨a,y,hy,e⟩:=ten_parts R B ho hf
  refine ⟨a,fun i hi=>?_⟩
  rw [e,Pi.add_apply,clean_orb h hi hy,add_zero,evalNodes_apply,eval_mul,eval_C]

theorem ten_clean_after_zero (R:Budget A) (B:Cut A U w n) (h:Heads A U w n)
    (ho:HasTreeOrderAtLeast A b 17) {f:Vec K 23} (hf:f∈zeroSpace A 10)
    {i:Fin 23} (ic:Clean A i) (inn:nodes A i≠0) (iz:f i=0):
    ∀j,Clean A j→f j=0:=by
  obtain ⟨a,t⟩:=ten_clean_trace R B h ho hf
  have gr:(grid K).eval (nodes A i)=0:=ic _ B.grid_paid
  have ne:=EarlyPort.leakage_nonzero_at_grid (nodes A i) inn gr
  have az:a=0:=(mul_eq_zero.mp ((t i ic).symm.trans iz)).resolve_right ne
  intro j jc
  rw [t j jc,az,zero_mul]

end
end RKCert.Paired.Seventeen.Early
