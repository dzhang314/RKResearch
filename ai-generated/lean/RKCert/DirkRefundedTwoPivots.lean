module
public import RKCert.DirkGradeTenPivots
@[expose] public section
namespace RKCert.Paired.OrdinaryTrace
open Polynomial RKCert.Endpoint
variable {K:Type*} [Field K] [CharZero K] {s p j g q m:ℕ}
variable {A:Fin s→Fin s→K} {b θ:Vec K s} {F:K[X]}

/-- A possibly *discounted* first clock trace pays two genuine chronological
commutator pivots and (m+1)+m primitive observations by grade g+m+1.
The weighted-support bill and both diagonal bills are explicit. -/
theorem two_pivots_of_paid_clock (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    (h:OrdinaryTrace A j θ F) (clockPaid:OrdinaryTrace A g (diag (nodes A) θ) (X*F))
    (nz:F≠0) (support:j+F.natDegree+5≤p) (matrix:g+3≤p) (comm:g+3≤q) (observations:g+m+1≤q)
    (clean:∀i,θ i≠0 → ∀f∈zeroSpace A q,f i=0) :
    ∃u v:K,u≠0 ∧ v≠0 ∧ v≠u ∧
      (∀k:Fin (m+1),(Paired.primitive (X^(k.val+1)*F)).eval u=0) ∧
      ∀k:Fin m,(Paired.primitive (X^(k.val+1)*((X-C u)*F))).eval v=0 :=by
  classical
  let c:=nodes A
  let t:=diag c θ
  have ht:OrdinaryTrace A g t (X*F):=clockPaid
  have gr(G:K[X]) (gn:G≠0) (dp:G.natDegree≤2) :
      ∃i,b i≠0 ∧ θ i≠0 ∧ G.eval (c i)≠0:=by
    apply h.exists_weighted_active_outside_roots ho nz G gn
    have:=natDegree_mul_le (p:=F) (q:=G);omega
  obtain ⟨l,_,nzθ,gx⟩:=gr X X_ne_zero (by rw [natDegree_X];decide)
  have tnon:t≠0:=by
    have present:t l≠0:=mul_ne_zero (by simpa using gx) nzθ
    exact fun e=>present (e ▸ rfl)
  obtain ⟨i,act,pre⟩:=exists_first_coordinate tnon
  have ai:c i≠0 ∧ θ i≠0:=mul_ne_zero_iff.mp act
  have ci:=clean i ai.2
  have di:=(ht.primitive_zero_at_first_clean ha ho (by omega) (by omega) act pre ci).1
  let u:=c i
  let t':=diag c t-u • t
  have h2:OrdinaryTrace A (g+1) t' (X*((X-C u)*F)):=by
    have hh:=ht.clock.sub ((ht.smul u).mono (by omega:g≤g+1))
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
  have diag':=(h2.primitive_zero_at_first_clean ha ho (by omega) (by omega) first pre' ci').1
  refine ⟨u,c i',ai.1,clki,sub_ne_zero.mp notu,?_,?_⟩
  · intro k
    have z:=ht.primitive_sequence_at_zero_diagonal ha pre di ci k.val (by have:=k.isLt;omega)
    simpa only [←mul_assoc,←pow_succ] using z
  · intro k
    have z:=h2.primitive_sequence_at_zero_diagonal ha pre' diag' ci' k.val (by have:=k.isLt;omega)
    simpa only [←mul_assoc,←pow_succ] using z
end RKCert.Paired.OrdinaryTrace
