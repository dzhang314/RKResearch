module
public import RKCert.DirkTenDoubleBand
public import RKCert.DirkOneFiberCut
@[expose] public section
namespace RKCert.Paired.Terminal
open Polynomial Module RKCert.OneEscape RKCert.Endpoint
variable {K:Type*} [Field K] [CharZero K] {s p:ℕ} {A:Fin s→Fin s→K} {b:Vec K s}
variable {V U:Submodule K (Vec K s)} {g w:Vec K s} {r n:ℕ}
noncomputable section

omit [CharZero K] in
/-- Squaring pairs of the early powers costs exactly grade eight, not twice
their clock degree in addition. The original larger core need not be a
coordinate algebra and no deliberately deleted row or chosen complement
appears in the proof. -/
private theorem square_in_band (h:TenDoubleBand A V U g w r n) :
    ∀k≤(r-1)+(r-1), (diag (nodes A)^k) (g*g)∈chain (diag (nodes A)) U w (n+2):=by
  let T:=diag (nodes A)
  have first:zeroSpace A 4=chain T V g r:=by simpa using h.early 0 (by decide)
  have paid:=((chain_le_iff (T:=T) (U:=V) (w:=g) r).mp first.ge).2
  have endp:zeroSpace A 8=chain T U w (n+2):=h.late 2 (by decide)
  intro k hk
  let a:=min k (r-1)
  let d:=k-a
  have rp:=h.early_pos
  have ha:a<r:=by dsimp [a];omega
  have hd:d<r:=by dsimp [d,a];omega
  have e:a+d=k:=by dsimp [a,d];omega
  have z:(T^k) (g*g)=(T^a) g*(T^d) g:=by
    ext i;simp only [T,Clock.pow_diag_apply,Pi.mul_apply];rw [←e,pow_add];ring
  rw [←endp,z]
  exact zeroSpace_mul (A:=A) (m:=4) (n:=4) (paid _ ha) (paid _ hd)

omit [CharZero K] in
/-- An actual double band with the one unpaid dimension concentrated only at
grade six produces a genuine nonzero quintic on all F10-dirty physical rows. -/
theorem TenDoubleBand.dirty_quintic (h:TenDoubleBand A V U g w r n)
    (ho:HasTreeOrderAtLeast A b p) (hp:15≤p) :
    ∃(P:K[X]) (θ:Vec K s),P≠0 ∧ OrdinaryTrace A 5 θ P ∧
      ∀i, θ i≠0→∀f∈zeroSpace A 10,f i=0:=by
  classical
  let c:=nodes A
  have rp:=h.early_pos
  have pos:=h.late_pos
  have us:=h.sites
  have dim:=Submodule.finrank_mono h.included
  have eqdim:=h.count
  obtain ⟨u,uu,L,ln,ld,ef⟩:=h.narrow
  obtain ⟨d,du,Q,qd,sq⟩:=Clock.overlapping_head_degree h.late_invariant h.normalized (by omega) (square_in_band h)
  obtain ⟨cut⟩:=Clock.core_cut_of_codimension h.included h.early_invariant h.late_invariant (by omega)
  let B:=cut.B
  have bn:B≠0:=cut.nz
  have bd:B.natDegree≤finrank K U-finrank K V:=cut.deg
  let R:=B*L
  have rn:R≠0:=mul_ne_zero bn ln
  have dr:R.natDegree≤1:=by
    have q:=natDegree_mul_le (p:=B) (q:=L); dsimp only [R];omega
  have first:zeroSpace A 4=chain (diag c) V g r:=by simpa [c] using h.early 0 (by decide)
  have later:zeroSpace A 6=chain (diag c) U w n:=by simpa [c] using h.late 0 (by decide)
  have last:zeroSpace A 10=chain (diag c) U w (n+4):=h.late 4 le_rfl
  have g4:g∈zeroSpace A 4:=by
    have e:=((chain_le_iff _).mp first.ge).2 0 rp
    simpa using e
  have w6:w∈zeroSpace A 6:=by
    have e:=((chain_le_iff _).mp later.ge).2 0 pos
    simpa using e
  have good:cut.good≤zeroSpace A 4:=cut.inside.trans h.early_paid
  have mixed {x y:Vec K s} (hx:x∈cut.good) (hy:y∈zeroSpace A 6):x*y∈cut.good:=
    cut.mixed (j:=4) (k:=6) h.early_paid h.late_invariant h.normalized h.sites last.le hx hy
  have up:zeroSpace A 4≤zeroSpace A 6:=zeroSpace_mono A (by decide)
  have alg:Clock.MulClosed cut.good:=fun _ hx _ hy=>mixed hx (up (good hy))
  obtain ⟨e,eg,ie⟩:=Clock.core_indicator alg
  have ew:=mixed eg w6
  have noCore (i:Fin s) (off:¬Clock.Live cut.good i) (hit:B.eval (c i)≠0) (a:Vec K s) (ha:a∈U):a i=0:=by
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
        have z:L.eval (c i)*w i=0:=by simpa [gg,noCore i live hit u uu] using (ef i).symm
        simp only [weightedEval_apply,Pi.mul_apply,ie,ite_eq_right live,zero_mul,mul_zero,R,eval_mul]
        rw [mul_assoc,z,mul_zero]
      rw [ewr];exact h.included (cut.inside (Clock.weightedEval_preserves cut.inv R ew))
    have de:R.degree<((Clock.headSites c w).card:WithBot ℕ):=by
      apply (natDegree_lt_iff_degree_lt rn).mp;change R.natDegree<(Clock.headSites (nodes A) w).card;omega
    exact rn (eq_zero_of_degree_lt_of_eval_finset_eq_zero _ de
      (Clock.scalar_head_vanishes h.late_invariant h.normalized mem))
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
  have match_g:g i=L.eval (c i)*w i:=by simpa [noCore i live hit u uu] using ef i
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

/-- Native absolute low-grade surplus, independent of the order-20 terminal
chart, signs of weights, and arithmetic properties of the field besides
characteristic zero. -/
theorem grade_three_ten_surplus (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p) (hp:15≤p):
    finrank K (zeroSpace A 3)+9≤finrank K (zeroSpace A 10):=by
  by_contra! small
  obtain ⟨_,_,_,_,_,_,h⟩:=ten_double_band_of_rank ha ho hp (by omega)
  obtain ⟨P,θ,nz,tr,clean⟩:=h.dirty_quintic ho hp
  obtain ⟨u,t,un,tn,tu,f,g⟩:=OrdinaryTrace.two_pivots_for_clean_quintic ha ho tr nz hp clean
  exact nz (RKCert.EndpointPhysical.quintic_four_three P tr.degree un tn tu f g)
end
end RKCert.Paired.Terminal

