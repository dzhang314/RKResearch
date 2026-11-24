module
public import RKCert.DirkSixHeads
public import RKCert.DirkRefundedTwoPivots
public import RKCert.DirkQuintic43
@[expose] public section
namespace RKCert.Paired.Terminal
open Module Polynomial RKCert.OneEscape RKCert.Endpoint
variable {K:Type*} [Field K] {s p:ℕ} {A:Fin s→Fin s→K} {b:Vec K s}
variable {U:Submodule K (Vec K s)} {w:Vec K s}

/-- The actual one-clock extension of grade nine; it need not be all of F₁₀. -/
def raisedNine (A:Fin s→Fin s→K) : Submodule K (Vec K s) :=
  zeroSpace A 9 ⊔ (zeroSpace A 9).map (diag (nodes A))

/-- On the true disjoint two-head chart, all grade-five pair products are
paid in the restricted raised-nine space (not necessarily the full grade
ten). The two cheap heads force a quartic and pay the trace of Xθ at
grade *five*, once more, rather than at grade six. -/
theorem nine_two_head_refund (inv:U.map (diag (nodes A))≤U)
    (alg:Clock.MulClosed U) (disj:∀i,Clock.Live U i→w i=0)
    (first:zeroSpace A 5=chain (diag (nodes A)) U w 2)
    (endBand:raisedNine A=chain (diag (nodes A)) U w 7)
    (out:¬(raisedNine A).map (diag (nodes A))≤raisedNine A)
    (products:∀a∈zeroSpace A 5,∀v∈zeroSpace A 5,a*v∈raisedNine A) :
    ∃P:K[X],∃θ:Vec K s,P≠0 ∧ P.natDegree≤4 ∧ (∀i,w i≠0→w i=P.eval (nodes A i)) ∧
      OrdinaryTrace A 5 θ P ∧ OrdinaryTrace A 5 (diag (nodes A) θ) (X*P) ∧
      ∀i,θ i≠0→∀f∈zeroSpace A 9,f i=0 :=by
  classical
  let C:=diag (nodes A)
  let F:=zeroSpace A
  have sites:7<(Clock.headSites (nodes A) w).card:=
    Clock.head_sites_of_noninvariant inv (by decide) (endBand ▸ out)
  have paid:=((chain_le_iff (T:=C) (U:=U) (w:=w) 2).mp first.ge)
  have w0:w∈F 5:=by simpa using paid.2 0 (by decide)
  have w1:C w∈F 5:=by simpa using paid.2 1 (by decide)
  have square (k:ℕ) (hk:k≤2):(C^k) (w*w)∈chain C U w 7:=by
    let i:=min k 1
    let l:=k-i
    have hi:i<2:=by dsimp [i];omega
    have hl:l<2:=by dsimp [i,l];omega
    have kl:i+l=k:=by dsimp [i,l];omega
    have eqn:(C^k) (w*w)=(C^i) w*(C^l) w:=by
      ext t
      simp only [C,Clock.pow_diag_apply,Pi.mul_apply]
      rw [←kl,pow_add];ring
    rw [eqn,←endBand];exact products _ (paid.2 _ hi) _ (paid.2 _ hl)
  obtain ⟨P,dP,val⟩:=Clock.multiplier_degree (a:=w) (c:=nodes A) disj sites square
  have nz:P≠0:=by
    rintro rfl
    have z:w=0:=by ext i;by_contra nn;exact nn ((val i nn).trans eval_zero)
    have card:(Clock.headSites (nodes A) w).card=0:=by simp [z,Clock.headSites]
    omega
  have deg:P.natDegree≤4:=by have:=dP.resolve_left nz;omega
  obtain ⟨e,eu,ind⟩:=Clock.core_indicator alg
  let z:Vec K s:=fun i=>P.eval (nodes A i)*e i
  have zu:z∈U:=Clock.poly_preserves inv P e eu
  let θ:=evalNodes A P-(w+z)
  have tr:OrdinaryTrace A 5 θ P:=(OrdinaryTrace.scalar A (by omega: P.natDegree≤5)).sub_pure ((F 5).add_mem w0 (paid.1 zu))
  have xp:(X*P).natDegree≤5:=natDegree_mul_le.trans (by rw [natDegree_X];omega)
  have ht:OrdinaryTrace A 5 (C θ) (X*P):=by
    have cc:C z∈U:=inv ⟨z,zu,rfl⟩
    have eq:C θ=evalNodes A (X*P)-(C w+C z):=by
      ext i;simp only [C,θ,diag_apply,Pi.sub_apply,Pi.add_apply,evalNodes_apply,eval_mul,eval_X];ring
    rw [eq]
    exact (OrdinaryTrace.scalar A xp).sub_pure ((F 5).add_mem w1 (paid.1 cc))
  refine ⟨P,θ,nz,deg,val,tr,ht,?_⟩
  intro i act f hf
  have live:¬Clock.Live U i:=by
    intro li;apply act;simp [θ,z,ind,li,disj i li]
  have off:w i=0:=by
    by_contra wi;apply act;simp [θ,z,ind,live,val i wi]
  have lift:zeroSpace A 9≤raisedNine A:=le_sup_left
  have covered:f∈chain C U w 7:=endBand ▸ lift hf
  obtain ⟨u,hu,_,_,eq⟩:=Clock.exists_head_poly covered
  have uz:u i=0:=by by_contra h;exact live ⟨u,hu,h⟩
  rw [eq i,uz,off,mul_zero,zero_add]

variable [CharZero K]
/-- Grade nine suffices, because the first clock trace was earned already
at grade five and its first pivot clock can be subtracted at grade six. -/
theorem no_disjoint_nine_two_head (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p) (hp:14≤p)
    (inv:U.map (diag (nodes A))≤U) (alg:Clock.MulClosed U) (disj:∀i,Clock.Live U i→w i=0)
    (first:zeroSpace A 5=chain (diag (nodes A)) U w 2)
    (endBand:raisedNine A=chain (diag (nodes A)) U w 7)
    (out:¬(raisedNine A).map (diag (nodes A))≤raisedNine A)
    (products:∀a∈zeroSpace A 5,∀v∈zeroSpace A 5,a*v∈raisedNine A) : False :=by
  obtain ⟨P,θ,nz,deg,_,tr,ht,clean⟩:=nine_two_head_refund inv alg disj first endBand out products
  obtain ⟨u,v,un,vn,vu,x,y⟩:=OrdinaryTrace.two_pivots_of_paid_clock (m:=3) ha ho tr ht nz
    (by omega) (by omega) (by decide) (by decide) clean
  exact nz (RKCert.EndpointPhysical.quintic_four_three P (by omega) un vn vu x y)
end RKCert.Paired.Terminal
