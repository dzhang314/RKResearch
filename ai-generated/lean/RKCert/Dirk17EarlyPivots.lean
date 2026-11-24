module
public import RKCert.Dirk17EarlyLeakage
public import RKCert.Dirk17ThreePortQuintic
public import RKCert.DirkGradeTenPivots
@[expose] public section
namespace RKCert.Paired.Seventeen.Early
open Polynomial RKCert.Endpoint RKCert.RadauEight
open scoped Classical
noncomputable section
variable {K:Type*} [Field K] [CharZero K]
variable {A:Fin 23→Fin 23→K} {b:Vec K 23} {U:Submodule K (Vec K 23)} {w:Vec K 23} {n:ℕ}

/-- The genuine clean grade-five witness is impossible. At the third
chronological mask its grade-ten commutator is zero on the earlier first
clean pivot, so the sole possible scalar leakage disappears before its
diagonal is refunded. No sign or order structure on K is used. -/
theorem clean_quintic_impossible (R:Budget A) (B:Cut A U w n) (h:Heads A U w n)
    (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17) {P:K[X]} {θ:Vec K 23}
    (tr:OrdinaryTrace A 5 θ P) (pn:P≠0) (good:∀i,θ i≠0→Clean A i):False:=by
  let c:=nodes A
  let D:=diag c
  have pay (G:K[X]) (gn:G≠0) (dg:G.natDegree≤3):evalNodes A G*θ≠0:=by
    obtain ⟨i,_,hi,qi⟩:=tr.exists_weighted_active_outside_roots ho pn G gn (by
      have e:=natDegree_mul_le (p:=P) (q:=G);have q:=tr.degree;omega)
    intro e
    have zi:=congrFun e i
    change G.eval (c i)*θ i=0 at zi
    exact (mul_ne_zero qi hi) zi
  let x:=D θ
  have hx:OrdinaryTrace A 6 x (X*P):=tr.clock
  have xeval:x=evalNodes A X*θ:=by ext i;simp [x,D,c]
  have xn:x≠0:=xeval ▸ pay X X_ne_zero (by rw [natDegree_X];decide)
  obtain ⟨i,ia,ip⟩:=exists_first_coordinate xn
  have iv:c i≠0 ∧ θ i≠0:=mul_ne_zero_iff.mp ia
  have ic:=good i iv.2
  have ide:= (hx.primitive_zero_at_first_clean ha ho (by decide) (by decide:6+2≤9) ia ip ic).1
  let u:=c i
  let y:=D x-u • x
  let G₂:=X*(X-C u)
  have yeval:y=evalNodes A G₂*θ:=by
    ext l;simp only [y,x,D,G₂,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.mul_apply,diag_apply,
      evalNodes_apply,eval_mul,eval_X,eval_sub,eval_C];dsimp [c];ring
  have g₂n:G₂≠0:=mul_ne_zero X_ne_zero (X_sub_C_ne_zero _)
  have g₂d:G₂.natDegree≤3:=natDegree_mul_le.trans (by rw [natDegree_X,natDegree_X_sub_C];decide)
  have yn:y≠0:=yeval ▸ pay G₂ g₂n g₂d
  have ty:OrdinaryTrace A 7 y (X*((X-C u)*P)):=by
    have e:=hx.clock.sub ((hx.smul u).mono (by decide:6≤7))
    simpa only [show X*(X*P)-C u*(X*P)=X*((X-C u)*P) by ring] using e
  obtain ⟨j,ja,jp⟩:=exists_first_coordinate yn
  have jv:c j≠0 ∧ c j≠u ∧ θ j≠0:=by
    rw [yeval,Pi.mul_apply,evalNodes_apply] at ja
    change (X*(X-C u)).eval (c j)*θ j≠0 at ja
    rw [eval_mul,eval_X,eval_sub,eval_X,eval_C] at ja
    obtain ⟨left,nz⟩:=mul_ne_zero_iff.mp ja
    obtain ⟨non,e⟩:=mul_ne_zero_iff.mp left
    exact ⟨non,sub_ne_zero.mp e,nz⟩
  have jc:=good j jv.2.2
  have jde:=(ty.primitive_zero_at_first_clean ha ho (by decide) (by decide:7+2≤9) ja jp jc).1
  let v:=c j
  let z:=D y-v • y
  let G₃:=X*((X-C u)*(X-C v))
  have zeval:z=evalNodes A G₃*θ:=by
    ext l
    simp only [z,yeval,D,G₂,G₃,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.mul_apply,diag_apply,
      evalNodes_apply,eval_mul,eval_X,eval_sub,eval_C]
    dsimp [c]
    ring
  have g₃n:G₃≠0:=mul_ne_zero X_ne_zero (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))
  have g₃d:G₃.natDegree≤3:=natDegree_mul_le.trans (by
    rw [natDegree_X]
    have bound:=natDegree_mul_le (p:=(X-C u:K[X])) (q:=X-C v)
    rw [natDegree_X_sub_C,natDegree_X_sub_C] at bound
    omega)
  have zn:z≠0:=zeval ▸ pay G₃ g₃n g₃d
  have tz:OrdinaryTrace A 8 z (X*((X-C u)*((X-C v)*P))):=by
    have e:=ty.clock.sub ((ty.smul v).mono (by decide:7≤8))
    simpa only [show X*(X*((X-C u)*P))-C v*(X*((X-C u)*P))=X*((X-C u)*((X-C v)*P)) by ring] using e
  obtain ⟨k,ka,kp⟩:=exists_first_coordinate zn
  have kv:c k≠0 ∧ c k≠u ∧ c k≠v ∧ θ k≠0:=by
    rw [zeval,Pi.mul_apply,evalNodes_apply] at ka
    change (X*((X-C u)*(X-C v))).eval (c k)*θ k≠0 at ka
    rw [eval_mul,eval_mul,eval_X,eval_sub,eval_sub,eval_X,eval_C,eval_C] at ka
    obtain ⟨first,nonθ⟩:=mul_ne_zero_iff.mp ka
    obtain ⟨nn,and⟩:=mul_ne_zero_iff.mp first
    obtain ⟨du,dv⟩:=mul_ne_zero_iff.mp and
    exact ⟨nn,sub_ne_zero.mp du,sub_ne_zero.mp dv,nonθ⟩
  have kc:=good k kv.2.2.2
  have pre (l:Fin 23)(hl:l < i):z l=0:=by
    have xx:x l=0:=ip l hl
    have yy:y l=0:=by simp [y,D,xx]
    simp [z,D,yy]
  have iz:z i=0:=by
    have yy:y i=0:=by simp [y,D,u]
    simp [z,D,yy]
  let f:=commutatorR (mat A) D z
  have fp:f∈zeroSpace A 10:=commutator_mem_zeroSpace ho 8 (by decide) tz.stage
  have fi:f i=0:=by
    change commutatorR (mat A) (diag c) z i=0
    rw [commutatorR_leading ha pre,iz,mul_zero]
  have fk:=ten_clean_after_zero R B h ho fp ic iv.1 fi k kc
  change commutatorR (mat A) (diag c) z k=0 at fk
  rw [commutatorR_leading ha kp] at fk
  have kde:A k k=0:=sq_eq_zero_iff.mp (neg_eq_zero.mp ((mul_eq_zero.mp fk).resolve_right ka))
  have i1:=hx.primitive_sequence_at_zero_diagonal ha ip ide ic 0 (by decide)
  have i2:=hx.primitive_sequence_at_zero_diagonal ha ip ide ic 1 (by decide)
  have i3:=hx.primitive_sequence_at_zero_diagonal ha ip ide ic 2 (by decide)
  have j1:=ty.primitive_sequence_at_zero_diagonal ha jp jde jc 0 (by decide)
  have j2:=ty.primitive_sequence_at_zero_diagonal ha jp jde jc 1 (by decide)
  have k1:=tz.primitive_sequence_at_zero_diagonal ha kp kde kc 0 (by decide)
  apply pn
  apply EarlyPort.quintic_three_two_one P tr.degree u v (c k) iv.1 jv.1 kv.1 jv.2.1 kv.2.1 kv.2.2.1
    (ic _ B.grid_paid) (jc _ B.grid_paid) (kc _ B.grid_paid)
  · simpa only [pow_zero,one_mul,u,c] using i1
  · simpa only [pow_one,pow_two,mul_assoc,u,c] using i2
  · simpa only [show (X:K[X])^3=X^2*X by rw [pow_succ],mul_assoc,u,c] using i3
  · simpa only [pow_zero,one_mul,v,c] using j1
  · simpa only [pow_one,pow_two,mul_assoc,v,c] using j2
  · simpa only [pow_zero,one_mul,c] using k1
end
end RKCert.Paired.Seventeen.Early
