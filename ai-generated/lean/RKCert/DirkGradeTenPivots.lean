module
public import RKCert.DirkCleanTracePivot
@[expose] public section
namespace RKCert.Paired
open Polynomial RKCert.Endpoint
variable {K:Type*} [Field K] [CharZero K] {s p j n:ℕ}
variable {A:Fin s→Fin s→K} {b θ:Vec K s} {F:K[X]}
namespace OrdinaryTrace
theorem primitive_sequence_at_zero_diagonal (h:OrdinaryTrace A j θ F)
    (ha:LowerArray A) {i:Fin s} (before:∀ k < i,θ k=0) (d:A i i=0)
    (clean:∀f∈zeroSpace A n, f i=0) (k:ℕ) (pay:j+k+1≤n) :
    (Paired.primitive (X^k*F)).eval (nodes A i)=0 :=by
  let v:=(diag (nodes A)^k) θ
  have pres:∀ l < i,v l=0:=by intro l hi;simp [v,Clock.pow_diag_apply,before l hi]
  have matz:mat A v i=0:=by simpa only [d,zero_mul] using causalDiag_mat ha i v pres
  have hz:=clean _ (zeroSpace_mono A pay (h.clock_pow k).primitive.pure)
  change (mat A v i)-(formalPrimitive (X^k*F)).eval (nodes A i)=0 at hz
  simpa only [matz,zero_sub,neg_eq_zero,formalPrimitive_eq_treePrimitive] using hz

/-- Two genuine first-surviving masks give four and three primitive tests.
Only a generous global order-15 payment is used to ensure actual support. -/
theorem two_pivots_for_clean_quintic (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    (h:OrdinaryTrace A 5 θ F) (nz:F≠0) (hp:15≤p)
    (clean:∀i,θ i≠0 → ∀f∈zeroSpace A 10,f i=0) :
    ∃u v:K,u≠0 ∧ v≠0 ∧ v≠u ∧
      (∀k:Fin 4,(Paired.primitive (X^(k.val+1)*F)).eval u=0) ∧
      ∀k:Fin 3,(Paired.primitive (X^(k.val+1)*((X-C u)*F))).eval v=0 :=by
  classical
  let c:=nodes A
  let t:=diag c θ
  have ht:OrdinaryTrace A 6 t (X*F):=h.clock
  have gr(G:K[X]) (gn:G≠0) (dp:G.natDegree≤2) :
      ∃i,b i≠0 ∧ θ i≠0 ∧ G.eval (c i)≠0:=by
    apply h.exists_weighted_active_outside_roots ho nz G gn
    have:=natDegree_mul_le (p:=F) (q:=G);have:=h.degree;omega
  obtain ⟨l,_,nzθ,gx⟩:=gr X X_ne_zero (by rw [natDegree_X];decide)
  have tnon:t≠0:=by
    have present:t l≠0:=mul_ne_zero (by simpa using gx) nzθ
    exact fun e=>present (e ▸ rfl)
  obtain ⟨i,act,pre⟩:=exists_first_coordinate tnon
  have ai:c i≠0 ∧ θ i≠0:=mul_ne_zero_iff.mp act
  have ci:=clean i ai.2
  have di:=(ht.primitive_zero_at_first_clean ha ho (by omega) (by decide) act pre ci).1
  let u:=c i
  let t':=diag c t-u • t
  have h2:OrdinaryTrace A 7 t' (X*((X-C u)*F)):=by
    have hh:=ht.clock.sub ((ht.smul u).mono (by decide:6≤7))
    simpa only [show X*(X*F)-C u*(X*F)=X*((X-C u)*F) by ring] using hh
  have coord(l:Fin s):t' l=(c l-u)*(c l*θ l):=by simp [t',t,diag_apply];ring
  obtain ⟨l',_,nzθ',gx'⟩:=gr (X*(X-C u)) (mul_ne_zero X_ne_zero (X_sub_C_ne_zero _))
    (natDegree_mul_le.trans (by rw [natDegree_X,natDegree_X_sub_C]))
  have factors:c l'≠0 ∧ (c l'-u)≠0:=by simpa only [eval_mul,eval_X,eval_sub,eval_C,mul_ne_zero_iff] using gx'
  have t'non:t'≠0:=by
    have present:t' l'≠0:=by rw [coord];exact mul_ne_zero factors.2 (mul_ne_zero factors.1 nzθ')
    exact fun e=>present (e ▸ rfl)
  obtain ⟨i',act',pre'⟩:=exists_first_coordinate t'non
  have first:=act'
  rw [coord] at act'
  have notu: c i'-u≠0 := (mul_ne_zero_iff.mp act').1
  obtain ⟨clki,activeθ⟩:=mul_ne_zero_iff.mp (mul_ne_zero_iff.mp act').2
  have ci':=clean i' activeθ
  have diag':=(h2.primitive_zero_at_first_clean ha ho (by omega) (by decide) first pre' ci').1
  refine ⟨u,c i',ai.1,clki,sub_ne_zero.mp notu,?_,?_⟩
  · intro k
    have z:=ht.primitive_sequence_at_zero_diagonal ha pre di ci k.val (by have:=k.isLt;omega)
    simpa only [←mul_assoc,←pow_succ] using z
  · intro k
    have z:=h2.primitive_sequence_at_zero_diagonal ha pre' diag' ci' k.val (by have:=k.isLt;omega)
    simpa only [←mul_assoc,←pow_succ] using z
end OrdinaryTrace
end RKCert.Paired

