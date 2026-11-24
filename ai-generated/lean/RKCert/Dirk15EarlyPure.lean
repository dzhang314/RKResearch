module
public import RKCert.Dirk15EarlyScalars
@[expose] public section
namespace RKCert.Paired.EarlyFifteen
open Polynomial Module RKCert.OneEscape RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K:Type*} [Field K] [CharZero K]
variable {A:Fin 20→Fin 20→K} {b:Vec K 20} {U:Submodule K (Vec K 20)} {w:Vec K 20} {r:ℕ}

theorem grade_ten_parts (H:Budget A) (B:Cut A U w r) (ho:HasTreeOrderAtLeast A b 15)
    {x:Vec K 20} (hx:x∈zeroSpace A 10) :
    ∃ P:K[X],∃ y∈orb A U w r 4, x=evalNodes A P+y ∧ P.natDegree≤7 ∧ P.eval 0=0 ∧
      ∀k≤4,unitIntegral (P*X^k)=0:=by
  have cl:=zeroSpace_le_treeSpace A 10 hx
  rw [B.e10] at cl
  obtain ⟨_,⟨a,rfl⟩,y,hy,e⟩:=Submodule.mem_sup.mp cl
  let P:=ofFn 8 a
  have d:P.natDegree≤7:=Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide:1≤8) a)
  have eq:x=evalNodes A P+y:=by
    change x=evalNodes A (ofFn (7+1) a)+y
    rw [evalNodes_ofFn]
    exact e.symm
  have yp:=B.pure hy
  have pure:evalNodes A P∈zeroSpace A 10:=by
    rw [show evalNodes A P=x-y by rw [eq];abel]
    exact Submodule.sub_mem _ hx yp
  have zero:(evalNodes A P) 0=0:=zeroSpace_first_of_row H.first 10 pure
  have at0:nodes A 0=0:=by simp [nodes,H.first]
  refine ⟨P,y,hy,eq,d,?_,fun k hk=>?_⟩
  · rwa [evalNodes_apply,at0] at zero
  · exact scalar_pure_unit_pair ho (d.trans (by decide)) pure (by rw [natDegree_X_pow];omega)

theorem grade_ten_shift (B:Cut A U w r) (h:Heads A U w r) (ho:HasTreeOrderAtLeast A b 15)
    {P Q:K[X]} (dP:P.natDegree≤7) (dQ:Q.natDegree≤7)
    {x y:Vec K 20} (hx:x∈orb A U w r 4) (hy:y∈orb A U w r 4)
    (e:diag (nodes A) (evalNodes A P+x)=evalNodes A Q+y) :
    ∃a:K,X*P-Q=C a*relation K:=by
  apply reduce_scalar B h ho
  · exact (natDegree_sub_le _ _).trans (max_le (natDegree_mul_le.trans (by rw [natDegree_X];omega)) (by omega))
  have e':evalNodes A (X*P-Q)=y-diag (nodes A) x:=by
    change evaluateColumn A (X*P-Q)=_
    rw [map_sub,←evaluateColumn_clock]
    change diag (nodes A) (evalNodes A P)-evalNodes A Q=_
    rw [map_add] at e
    abel_nf at e ⊢
    linear_combination e
  rw [e']
  apply Submodule.sub_mem _ (orb_le (by decide:4≤5) hy)
  exact (orb_step h 4).le ((le_sup_right:(orb A U w r 4).map (diag (nodes A))≤_) (Submodule.mem_map_of_mem hx))

theorem shift_test {P Q:K[X]} {a:K} (shift:X*P-Q=C a*relation K)
    (k:ℕ) (hk:k≤6) (obs:unitIntegral (Q*X^k)=0):
    unitIntegral (P*X^(k+1))=0:=by
  have eq:X*P=Q+a • relation K:=by rw [←smul_eq_C_mul] at shift;linear_combination shift
  rw [show P*X^(k+1)=(X*P)*X^k by rw [pow_succ];ring,eq,add_mul,smul_mul_assoc,
    map_add,map_smul,obs,relation_test _ (by rw [natDegree_X_pow];omega),smul_zero,zero_add]

/-- Three adjacent paid products are enough. Two clock shifts refund the
fifth and sixth moments of the original scalar part without any appeal to
a positivity argument or a new Jacobi recurrence. -/
theorem strip_ladder (R:Budget A) (B:Cut A U w r) (h:Heads A U w r)
    (ho:HasTreeOrderAtLeast A b 15) (x:ℕ→Vec K 20) {n:ℕ} (n2:2≤n)
    (pure:∀ k≤n,x k∈zeroSpace A 10)
    (step:∀ k<n,diag (nodes A) (x k)=x (k+1)) :
    ∀ k≤n,x k∈orb A U w r 4:=by
  have parts (k:Fin (n+1)):=grade_ten_parts R B ho (pure k.val (by have:=k.isLt;omega))
  choose P y hm e d z moment using parts
  have sh (k:Fin n) : ∃a:K,X*P k.castSucc-P k.succ=C a*relation K:=by
    apply grade_ten_shift B h ho (d _) (d _) (hm _) (hm _)
    rw [←e,←e]
    exact step k.val k.isLt
  let i0:Fin n:=⟨0,by omega⟩
  let i1:Fin n:=⟨1,by omega⟩
  obtain ⟨a,sh0⟩:=sh i0
  obtain ⟨a',sh1⟩:=sh i1
  have q5:unitIntegral (P i0.succ*X^5)=0:=
    shift_test sh1 4 (by decide) (moment i1.succ 4 le_rfl)
  have m0:P i0.castSucc=0:=anchored_gram _ (d _) (z _) (fun k hk=>by
    rcases (show k≤4∨k=5∨k=6 by omega) with h4|rfl|rfl
    · exact moment _ _ h4
    · exact shift_test sh0 4 (by decide) (moment i0.succ 4 le_rfl)
    · exact shift_test sh0 5 (by decide) q5)
  have advance (k:Fin n) (before:P k.castSucc=0):P k.succ=0:=by
    obtain ⟨α,e'⟩:=sh k
    rw [before,mul_zero,zero_sub] at e'
    have az:α=0:=by
      by_contra hn
      have eq:=congrArg natDegree e'
      rw [natDegree_neg,natDegree_C_mul hn,relation_degree] at eq
      have x:=d k.succ
      omega
    simpa [az] using e'
  have all (k:ℕ) (hk:k<n+1):P ⟨k,hk⟩=0:=by
    induction k with
    | zero => exact m0
    | succ k ih =>
      let i:Fin n:=⟨k,by omega⟩
      exact advance i (ih (by omega))
  intro k hk
  let i:Fin (n+1):=⟨k,by omega⟩
  change x i.val∈orb A U w r 4
  have eq:=e i
  rw [all k (by omega),show evalNodes A (0:K[X])=0 from by ext j;simp,zero_add] at eq
  exact eq ▸ hm i

/-- A localized original F10 product must belong to the genuine invariant
core. Its own clock supplies the same two refunds by a scalar recurrence. -/
theorem localized_ten (R:Budget A) (B:Cut A U w r) (h:Heads A U w r)
    (ho:HasTreeOrderAtLeast A b 15) {x:Vec K 20} (pure:x∈zeroSpace A 10) {a:K}
    (localc:∀ i,nodes A i≠a→x i=0) : x∈U:=by
  obtain ⟨P,y,hy,e,d,z,mom⟩:=grade_ten_parts R B ho pure
  have ex:diag (nodes A) x=a • x:=by
    ext i
    by_cases eq:nodes A i=a
    · simp [eq]
    · simp [localc i eq]
  have ya:a • y∈orb A U w r 4:=Submodule.smul_mem _ a hy
  have sh:∃α:K,X*P-a • P=C α*relation K:=by
    have dj:(a • P).natDegree≤7:=by rw [smul_eq_C_mul];exact (natDegree_C_mul_le _ _).trans d
    apply grade_ten_shift B h ho d dj hy ya
    rw [←e,ex,e]
    change a • (evaluateColumn A P+y)=evaluateColumn A (a • P)+a • y
    rw [map_smul,smul_add]
  obtain ⟨α,shift⟩:=sh
  have test (k:ℕ) (hk:k≤6):unitIntegral (P*X^k)=0:=by
    induction k with
    | zero => exact mom 0 (by decide)
    | succ k ih =>
      have p:=ih (by omega)
      exact shift_test shift k (by omega) (by rw [smul_mul_assoc,map_smul,p,smul_zero])
  have p0:=anchored_gram P d z test
  have xy:x=y:=by rw [e,p0,show evalNodes A (0:K[X])=0 by ext i;simp,zero_add]
  exact Clock.localized_mem h.inv h.normal B.sites (xy ▸ hy) localc

end
end RKCert.Paired.EarlyFifteen
