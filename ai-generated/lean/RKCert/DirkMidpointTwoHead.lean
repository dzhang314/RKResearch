module
public import RKCert.DirkMidpointFactor
@[expose] public section
namespace RKCert.Paired.Terminal.MidpointHead
open Polynomial Module RKCert.OneEscape RKCert.Endpoint
variable {K:Type*} [Field K] [CharZero K] {s m:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b w:Vec K (s+1)} {U:Submodule K (Vec K (s+1))}
noncomputable section
set_option maxHeartbeats 2400000

/-- A two-cheap-power head has all three original grade-ten square
products. Two contiguous tail links, not a postulated vanishing scalar
component of F10, make them eligible for the head-multiplier identity. -/
theorem no_two_head (h:MidpointHead A m U w 2) (hm:m=7 ∨ m=8)
    (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m)
    (cut:∀i,Clock.Live U i → w i=0) (mul:Clock.MulClosed U) :False:=by
  classical
  let T:=diag (nodes A)
  have lo:7≤m:=by rcases hm with rfl|rfl <;>omega
  have hi:m≤8:=by rcases hm with rfl|rfl <;>omega
  have w5:=h.head_paid (by omega)
  have c5:T w∈zeroSpace A 5:=by
    rw [h.band 5 le_rfl (by omega)]
    have y:=((chain_le_iff (T:=T) (U:=U) (w:=w) (2+(5-5))).mp le_rfl).2 1 (by decide)
    simpa using y
  have id1:T (w*w)=T w*w:=by ext i;simp [T,diag_apply];ring
  have id2:T (T (w*w))=T w*T w:=by ext i;simp [T,diag_apply];ring
  let O:=chain T U w (2+(10-5))
  have dec(x:Vec K (s+1)) (hx:x∈zeroSpace A 10)
      (cl:∀i,(∀f∈zeroSpace A 5,f i=0)→x i=0) :
      ∃H:K[X],∃v∈O,LobattoPaidTail m (2*m-11) H ∧ x=evalNodes A H+v :=by
    have g:=h.pure_decompose hm ha ho he (q:=10) (by omega) (by omega) hx cl
    simpa only [show 2*m-10-1=2*m-11 by omega] using g
  obtain ⟨H₀,x₀,h₀,z₀,e₀⟩:=dec (w*w) (zeroSpace_mul (A:=A) (m:=5) (n:=5) w5 w5)
    (fun i cl=>by rw [Pi.mul_apply,cl w w5,zero_mul])
  obtain ⟨H₁,x₁,h₁,z₁,e₁⟩:=dec (T (w*w)) (by rw [id1];exact zeroSpace_mul (A:=A) (m:=5) (n:=5) c5 w5)
    (fun i cl=>by rw [id1,Pi.mul_apply,cl w w5,mul_zero])
  obtain ⟨H₂,x₂,h₂,z₂,e₂⟩:=dec (T (T (w*w))) (by rw [id2];exact zeroSpace_mul (A:=A) (m:=5) (n:=5) c5 c5)
    (fun i cl=>by rw [id2,Pi.mul_apply,cl _ c5,zero_mul])
  have link0:=h.link_products hm ha ho he z₀.degree z₁.degree h₀ h₁ e₀ e₁
  have link1:=h.link_products hm ha ho he z₁.degree z₂.degree h₁ h₂ e₁ e₂
  have vanish:H₀=0 ∧ H₁=0 ∧ H₂=0:=by
    rcases hm with rfl|rfl
    · exact lobatto7_tail_two_links z₀ z₁ z₂ link0 link1
    · have zz:=lobatto8_tail_one_link z₀ z₁ link0
      exact ⟨zz.1,zz.2,z₂.eq_zero_of_prev (by decide) zz.2 link1⟩
  have hs:=h.physical_head_site_bound (hm.imp_right Or.inl) ha ho he (q:=2*m-3) (by omega) (by omega)
  have band(k:ℕ) (hk:k≤2):(T^k) (w*w)∈O:=by
    interval_cases k
    · rw [pow_zero,Module.End.one_eq_id,LinearMap.id_apply,e₀,vanish.1,show evalNodes A (0:K[X])=0 from by ext i;simp,zero_add]
      exact h₀
    · rw [pow_one,e₁,vanish.2.1,show evalNodes A (0:K[X])=0 from by ext i;simp,zero_add]
      exact h₁
    · rw [pow_succ',pow_one,Module.End.mul_eq_comp,LinearMap.comp_apply,e₂,vanish.2.2,show evalNodes A (0:K[X])=0 from by ext i;simp,zero_add]
      exact h₂
  obtain ⟨P,dp,val⟩:=Clock.multiplier_degree (c:=nodes A) cut (by omega:2+(10-5)<(Clock.headSites (nodes A) w).card) band
  have degrees:P.natDegree≤4:=by
    rcases dp with z|z
    · simp [z]
    · omega
  have many:m<(Clock.headSites (nodes A) w).card:=by omega
  have fact:=h.nodal_factor hm ha ho he cut val (by omega) many
  exact h.factor_kills hm ha ho he cut mul fact val (Or.inr ⟨by decide,degrees⟩)

end
end RKCert.Paired.Terminal.MidpointHead

