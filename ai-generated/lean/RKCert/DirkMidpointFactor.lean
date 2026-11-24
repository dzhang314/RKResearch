module
public import RKCert.DirkMidpointCardinal
@[expose] public section
namespace RKCert.Paired.Terminal.MidpointHead
open Polynomial Module RKCert.OneEscape RKCert.Endpoint
variable {K:Type*} [Field K] [CharZero K] {s m r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b w:Vec K (s+1)} {U:Submodule K (Vec K (s+1))}
noncomputable section

omit [CharZero K] in
theorem vanish_on_head {H:K[X]} (small:H.natDegree<(Clock.headSites (nodes A) w).card)
    (zero:∀i,w i≠0 → H.eval (nodes A i)=0) : H=0 :=by
  classical
  let S:=Clock.headSites (nodes A) w
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero H (Subtype.val_injective (p:=(·∈S)))
  · intro z
    obtain ⟨i,hi,e⟩:=Finset.mem_image.mp z.property
    exact e ▸ zero i (Finset.mem_filter.mp hi).2
  · simpa [S] using small

theorem nodal_factor (h:MidpointHead A m U w r) (hm:m=7 ∨ m=8)
    (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m)
    (sep:∀i,Clock.Live U i → w i=0) {P:K[X]} (wP:∀i,w i≠0→w i=P.eval (nodes A i))
    (dP:P.natDegree+r+(m-5)≤m+1) (many:m<(Clock.headSites (nodes A) w).card) : P ∣ lobatto m :=by
  classical
  have seven:7≤m:=by rcases hm with rfl|rfl <;>decide
  obtain ⟨β,Q,bn,dQ,card⟩:=h.head_cardinal hm ha ho he sep
  have QP: (Q*P).natDegree≤m:=natDegree_mul_le.trans (by omega)
  have eqn:C β*lobatto m+Q*P=0:=by
    apply vanish_on_head (w:=w) (A:=A)
    · exact (natDegree_add_le _ _).trans_lt ((max_le ((natDegree_C_mul_le _ _).trans (lobatto_degree (by omega))) QP).trans_lt many)
    · intro i wi
      simpa only [eval_add,eval_mul,eval_C,←wP i wi] using card i wi
  refine ⟨-C β⁻¹*Q,?_⟩
  have val:=congrArg (fun X:K[X]=>C β⁻¹*X) eqn
  calc
    lobatto m = C β⁻¹*(C β*lobatto m) := by
      rw [←mul_assoc,←C_mul,inv_mul_cancel₀ bn,C_1,one_mul]
    _ = P*(-C β⁻¹*Q) := by linear_combination val

omit [CharZero K] in
theorem select_live (h:MidpointHead A m U w r) (hm:5≤m) (i:Fin (s+1))
    (hi:∃f∈zeroSpace A m,f i≠0) : Clock.Live U i ∨ w i≠0 :=by
  classical
  obtain ⟨f,hf,hi⟩:=hi
  rw [h.band m hm le_rfl] at hf
  obtain ⟨u,hu,Q,_,rep⟩:=Clock.exists_head_poly hf
  by_cases wu:w i=0
  · left;refine ⟨u,hu,?_⟩;intro uz;apply hi;rw [rep i,uz,wu,mul_zero,zero_add]
  · exact Or.inr wu

/-- Attach to the chosen head the actual class indicators of the core.
The resulting genuine pure column agrees with the known factor on
every dirty physical stage. -/
theorem factor_kills (h:MidpointHead A m U w r) (hm:m=7 ∨ m=8)
    (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m)
    (sep:∀i,Clock.Live U i → w i=0) (mul:Clock.MulClosed U)
    {P:K[X]} (fact:P∣lobatto m) (wP:∀i,w i≠0→w i=P.eval (nodes A i))
    (ready:(m=8 ∧ P.natDegree≤5) ∨ (2≤r ∧ P.natDegree≤4)) : False :=by
  classical
  have seven:7≤m:=by rcases hm with rfl|rfl <;>decide
  let c:=nodes A
  obtain ⟨e,heU,ind⟩:=Clock.core_indicator mul
  have masked(T:K[X]):weightedEval c e T∈U :=by
    have hmem:=Clock.poly_preserves h.invariant T e heU
    simpa only [show weightedEval c e T=(fun i=>T.eval (nodes A i)*e i) by ext i;simp [c]] using hmem
  by_cases paid:5+3≤m
  · apply no_lobatto_factor_mask_on_dirty hm ha ho he fact (j:=5) (by rcases ready with p|p <;>omega) paid
      ((zeroSpace A 5).add_mem (h.head_paid (by omega)) (h.paid (masked P)))
    intro i dirty
    rcases h.select_live (by omega) i dirty with live|wi
    · rw [Pi.add_apply,weightedEval_apply,sep i live,ind i,ite_eq_left live,mul_one,zero_add]
    · have inactive:¬Clock.Live U i:=fun e=>wi (sep i e)
      rw [Pi.add_apply,weightedEval_apply,ind i,ite_eq_right inactive,mul_zero,add_zero,wP i wi]
  · obtain ⟨r2,dp⟩ : 2≤r ∧ P.natDegree≤4:=by rcases ready with p|p <;>omega
    have cheap : diag c w∈zeroSpace A 5 :=by
      rw [h.band 5 le_rfl (by omega)]
      have y:=((chain_le_iff (T:=diag c) (U:=U) (w:=w) (r+(5-5))).mp le_rfl).2 1 (by omega)
      simpa using y
    apply no_shifted_lobatto_factor_mask hm ha ho he fact (j:=5)
      (natDegree_mul_le.trans (by rw [natDegree_X];omega)) (by omega)
      ((zeroSpace A 5).add_mem cheap (h.paid (masked (X*P))))
    intro i dirty
    rcases h.select_live (by omega) i dirty with live|wi
    · rw [Pi.add_apply,diag_apply,weightedEval_apply,eval_mul,eval_X,sep i live,ind i,ite_eq_left live,mul_one,mul_zero,zero_add]
    · have inactive:¬Clock.Live U i:=fun e=>wi (sep i e)
      rw [Pi.add_apply,diag_apply,weightedEval_apply,ind i,ite_eq_right inactive,mul_zero,add_zero,wP i wi]

end
end RKCert.Paired.Terminal.MidpointHead

