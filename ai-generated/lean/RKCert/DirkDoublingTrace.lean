module
public import RKCert.DirkFourEightSurplus
public import RKCert.DirkNineProductObstruction
@[expose] public section
namespace RKCert.Paired.Terminal
open Module Polynomial RKCert.OneEscape
variable {K:Type*} [Field K] [CharZero K] {s p j d:ℕ} {A:Fin s→Fin s→K} {b:Vec K s}
noncomputable section
set_option maxRecDepth 3500
/-- A full band with only unit gains, including ordinary grade 2j, supplies
a profile of degree reduced by the length r of the initial head. The trace
is already genuine at grade j and is supported only on rows that are clean
through the actual end of the band. No strict triangle or signs are used. -/
theorem doubling_clean_trace (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    (lo:4≤j) (twice:j≤d) (order:j+d+1≤p)
    (flat:∀a<d,finrank K (zeroSpace A (j+a+1))≤finrank K (zeroSpace A (j+a))+1):
    ∃r:ℕ,0<r ∧ j/2≤r+1 ∧ ∃P:K[X],∃θ:Vec K s,P≠0 ∧ P.natDegree+r≤j+1 ∧
      OrdinaryTrace A j θ P ∧ (∀i,θ i≠0→∀f∈zeroSpace A (j+d),f i=0):=by
  classical
  let F:=zeroSpace A;let C:=diag (nodes A)
  have non(a:ℕ)(aa:a≤d):¬(F (j+a)).map C≤F (j+a):=by
    intro inc
    have hc:∀v∈F (j+a),C v∈F (j+a):=fun v hv=>inc ⟨v,hv,rfl⟩
    cases a with
    | zero=>
      have gain:=dirk_forward_invariant_outgoing ha ho (j:=j) (by omega) (F j) le_rfl hc
      have cap:=flat 0 (by omega)
      change finrank K (F (j+1))≤finrank K (F j)+1 at cap
      change finrank K (F j)+j/2≤finrank K (F (j+1)) at gain;omega
    | succ a=>
      have gain:=dirk_forward_invariant_incoming ha ho (j:=j+(a+1)) (by omega) hc
      have cap:=flat a (by omega)
      change finrank K (F (j+(a+1)-1))+(j+(a+1)-1)/2≤finrank K (F (j+(a+1))) at gain
      rw [show j+(a+1)-1=j+a by omega,show j+(a+1)=j+a+1 by omega] at gain
      change finrank K (F (j+a+1))≤finrank K (F (j+a))+1 at cap;omega
  have start:¬(F j).map C≤F j:=by simpa only [Nat.add_zero] using non 0 (by omega)
  have step:finrank K (F (j+1))≤finrank K (F j)+1:=by simpa only [Nat.add_zero] using flat 0 (by omega)
  obtain ⟨r,U,w,hr,inv,uf,_,base,wp,_,dim,norm,_⟩:=Clock.ordinary_normal_head A j step start
  have herm:=dirk_forward_invariant_outgoing ha ho (j:=j) (by omega) U uf (fun v hv=>inv ⟨v,hv,rfl⟩)
  change finrank K (F j)=finrank K U+r at dim
  change finrank K U+j/2≤finrank K (F (j+1)) at herm
  have lower:j/2≤r+1:=by omega
  have band:=Clock.ordinary_staircase inv hr base flat (fun k h=>non k h.le)
  have squareBand:F (j+j)=chain C U w (r+j):=band j twice
  have sites:=Clock.head_sites_of_noninvariant inv (by omega:0<r+j) (squareBand ▸ non j twice)
  have keep(u:Vec K s)(hu:u∈U)(x:Vec K s)(hx:x∈F j):u*x∈U:=Clock.core_mul inv uf norm sites squareBand.le hu hx
  have alg:Clock.MulClosed U:=fun u hu v hv=>keep u hu v (uf hv)
  have w0:w∈F j:=by simpa only [pow_zero,one_apply_eq_self] using wp 0 hr
  obtain ⟨v,_,disjoint,same⟩:=Clock.disjoint_head inv alg (fun u hu=>keep u hu w w0)
  have first:F j=chain C U v r:=base.trans (same r).symm
  have sq:F (j+j)=chain C U v (r+j):=squareBand.trans (same (r+j)).symm
  have endBand:F (j+d)=chain C U v (r+d):=(band d le_rfl).trans (same (r+d)).symm
  have sites':=Clock.head_sites_of_noninvariant inv (by omega:0<r+j) (sq ▸ non j twice)
  have paid:=((chain_le_iff (T:=C) (U:=U) (w:=v) r).mp first.ge).2
  have v0:v∈F j:=by simpa only [pow_zero,one_apply_eq_self] using paid 0 hr
  have power(k:ℕ)(hk:k≤(r-1)+(r-1)):(C^k) (v*v)∈chain C U v (r+j):=by
    let i:=min k (r-1);let l:=k-i
    have hi:i<r:=by dsimp [i];omega
    have hl:l<r:=by dsimp [i,l];omega
    have kl:i+l=k:=by dsimp [i,l];omega
    have eqn:(C^k) (v*v)=(C^i) v*(C^l) v:=by
      ext t;simp only [C,Clock.pow_diag_apply,Pi.mul_apply];rw [←kl,pow_add];ring
    rw [eqn,←sq];exact zeroSpace_mul (paid _ hi) (paid _ hl)
  obtain ⟨P,small,val⟩:=Clock.multiplier_degree (a:=v) (c:=nodes A) disjoint sites' power
  have pn:P≠0:=by
    rintro rfl
    have eq:v=0:=by ext i;by_contra nn;exact nn ((val i nn).trans eval_zero)
    have card:(Clock.headSites (nodes A) v).card=0:=by simp [eq,Clock.headSites]
    omega
  have degree:P.natDegree+r≤j+1:=by have:=small.resolve_left pn;omega
  obtain ⟨e,eu,ind⟩:=Clock.core_indicator alg
  let z:Vec K s:=fun i=>P.eval (nodes A i)*e i
  have zu:z∈U:=Clock.poly_preserves inv P e eu
  let θ:=evalNodes A P-(v+z)
  have trace:OrdinaryTrace A j θ P:=(OrdinaryTrace.scalar A (by omega:P.natDegree≤j)).sub_pure ((F j).add_mem v0 (uf zu))
  refine ⟨r,hr,lower,P,θ,pn,degree,trace,?_⟩
  intro i active f hf
  have live:¬Clock.Live U i:=by intro li;apply active;simp [θ,z,ind,li,disjoint i li]
  have off:v i=0:=by by_contra vi;apply active;simp [θ,z,ind,live,val i vi]
  change f∈F (j+d) at hf
  rw [endBand] at hf
  obtain ⟨u,hu,_,_,eq⟩:=Clock.exists_head_poly hf
  have uz:u i=0:=by by_contra h;exact live ⟨u,hu,h⟩
  rw [eq i,uz,off,mul_zero,zero_add]

theorem grade_four_nine_surplus (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p) (hp:13≤p):
    finrank K (zeroSpace A 4)+6≤finrank K (zeroSpace A 9):=by
  by_contra! small
  have flat(a:ℕ)(aa:a<5):finrank K (zeroSpace A (4+a+1))≤finrank K (zeroSpace A (4+a))+1:=by
    have q:=flag_gain ha ho (a:=4) (n:=4+a) (by decide) (by omega) (by omega)
    have t:=flag_gain ha ho (a:=4+a+1) (n:=9) (by omega) (by omega) (by omega)
    omega
  obtain ⟨r,hr,_,P,θ,pn,dP,trace,clean⟩:=doubling_clean_trace ha ho (j:=4) (d:=5) (by decide) (by decide) (by omega) flat
  obtain ⟨u,v,un,vn,vu,first,next⟩:=OrdinaryTrace.two_pivots_of_paid_clock (m:=3) ha ho trace trace.clock pn
    (by omega) (by omega) (by decide) (by decide) clean
  exact pn (RKCert.EndpointPhysical.quintic_four_three P (by omega) un vn vu first next)
end
end RKCert.Paired.Terminal
