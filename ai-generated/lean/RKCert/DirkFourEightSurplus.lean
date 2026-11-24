module
public import RKCert.DirkEightPortField
public import RKCert.DirkParityFloor
public import RKCert.CoreSupport
@[expose] public section
namespace RKCert.Paired.Terminal
open Module Polynomial RKCert.OneEscape
set_option maxHeartbeats 2000000
variable {K:Type*} [Field K] [CharZero K] {s p:ℕ}
variable {A:Fin s→Fin s→K} {b:Vec K s}
omit [CharZero K] in
private theorem eight_extra_head_sites {c v:Vec K s} {U F:Submodule K (Vec K s)} {n:ℕ}
    (pos:0<n) (inv:U.map (diag c)≤U) (eqn:F=chain (diag c) U v n)
    (out:¬ F.map (diag c)≤F) : n<(Clock.headSites c v).card := by
  have paid:=((chain_le_iff (T:=diag c) (U:=U) (w:=v) n).mp eqn.ge).2
  apply Clock.more_sites_than_paid paid
  intro head
  apply out
  apply le_sup_right.trans
  rw [eqn,chain_sup_map inv pos]
  change chain (diag c) U v n ⊔ Submodule.span K {(diag c ^ n) v} ≤ chain (diag c) U v n
  exact sup_le le_rfl ((Submodule.span_singleton_le_iff_mem ..).mpr (eqn ▸ head))

/-- A genuine grade-4…8 single-growth band over a characteristic-zero
field would supply a free quartic at a *physically attained* exceptional
ratio. In particular fields without a square root of -6 pay five ranks,
even when the last grade-eight space was initially allowed invariant. -/
theorem grade_four_eight_surplus (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p) (hp:13≤p)
    (field:RKCert.EndpointPhysical.NoExceptionalRatio K):finrank K (zeroSpace A 4)+5≤finrank K (zeroSpace A 8):=by
  classical
  by_contra! small
  let F:=zeroSpace A
  let C:=diag (nodes A)
  have flat(a:ℕ)(aa:a<4):finrank K (F (4+a+1))≤finrank K (F (4+a))+1 :=by
    have g1:=flag_gain ha ho (a:=4) (n:=4+a) (by decide) (by omega) (by omega)
    have g2:=flag_gain ha ho (a:=4+a+1) (n:=8) (by omega) (by omega) (by omega)
    dsimp only [F];omega
  have non(a:ℕ)(aa:a≤4):¬(F (4+a)).map C≤F (4+a):=by
    intro inc
    have hc:∀v∈F (4+a), C v∈F (4+a):=fun v hv=>inc ⟨v,hv,rfl⟩
    cases a with
    | zero=>
      have gain:=dirk_forward_invariant_outgoing ha ho (j:=4) (by omega) (F 4) le_rfl hc
      have cap:=flat 0 (by decide)
      change finrank K (F 5)≤finrank K (F 4)+1 at cap
      change finrank K (F 4)+2≤finrank K (F 5) at gain
      omega
    | succ a=>
      have gain:=dirk_forward_invariant_incoming ha ho (j:=4+(a+1)) (by omega) hc
      have cap:=flat a (by omega)
      change finrank K (F (4+(a+1)-1))+(4+(a+1)-1)/2≤finrank K (F (4+(a+1))) at gain
      rw [show 4+(a+1)-1=4+a by omega,show 4+(a+1)=4+a+1 by omega] at gain
      omega
  obtain ⟨r,U,w,hr,hU,hUF,_,base,_,_,_,normalized,_⟩:=Clock.ordinary_normal_head A 4 (flat 0 (by decide)) (non 0 (by decide))
  have last:F 8=chain C U w (r+4):=Clock.ordinary_staircase hU hr base flat (fun k h=>non k h.le) 4 le_rfl
  have count:=eight_extra_head_sites (by omega) hU last (non 4 le_rfl)
  have keep(u:Vec K s)(hu:u∈U)(x:Vec K s)(hx:x∈F 4):u*x∈U:=Clock.core_mul hU hUF normalized count last.le hu hx
  have alg:Clock.MulClosed U:=fun u hu v hv=>keep u hu v (hUF hv)
  have w0:w∈F 4 := by
    have hh:=((chain_le_iff (T:=C) (U:=U) (w:=w) r).mp base.ge).2 0 hr
    simpa using hh
  obtain ⟨v,_,disjoint,same⟩:=Clock.disjoint_head hU alg (fun u hu=>keep u hu w w0)
  have first:F 4=chain C U v r:=base.trans (same r).symm
  have ending:F 8=chain C U v (r+4):=last.trans (same (r+4)).symm
  have sites:=eight_extra_head_sites (by omega) hU ending (non 4 le_rfl)
  have paid:=((chain_le_iff (T:=C) (U:=U) (w:=v) r).mp first.ge).2
  have v0:v∈F 4:=by simpa using paid 0 hr
  have power (k:ℕ) (hk:k≤(r-1)+(r-1)):(C^k) (v*v)∈chain C U v (r+4):=by
    let i:=min k (r-1)
    let l:=k-i
    have hi:i<r:=by dsimp [i];omega
    have hl:l<r:=by dsimp [i,l];omega
    have kl:i+l=k:=by dsimp [i,l];omega
    have eqn:(C^k) (v*v)=(C^i) v*(C^l) v:=by
      ext t
      simp only [C,Clock.pow_diag_apply,Pi.mul_apply]
      rw [←kl,pow_add];ring
    rw [eqn,←ending];exact zeroSpace_mul (paid _ hi) (paid _ hl)
  obtain ⟨P,dP,val⟩:=Clock.multiplier_degree (a:=v) (c:=nodes A) disjoint sites power
  have nz:P≠0:=by
    rintro rfl
    have z:v=0:=by ext i;by_contra nn;exact nn ((val i nn).trans eval_zero)
    have card:(Clock.headSites (nodes A) v).card=0:=by simp [z,Clock.headSites]
    omega
  have deg:P.natDegree≤4:=by have:=dP.resolve_left nz;omega
  obtain ⟨e,eu,ind⟩:=Clock.core_indicator alg
  let z:Vec K s:=fun i=>P.eval (nodes A i)*e i
  have zu:z∈U:=Clock.poly_preserves hU P e eu
  let θ:=evalNodes A P-(v+z)
  have tr:OrdinaryTrace A 4 θ P:=(OrdinaryTrace.scalar A deg).sub_pure ((F 4).add_mem v0 (hUF zu))
  have clean(i:Fin s)(act:θ i≠0)(f:Vec K s)(hf:f∈F 8):f i=0:=by
    have live:¬Clock.Live U i:=by
      intro li;apply act
      simp [θ,z,ind,li,disjoint i li]
    have off:v i=0:=by
      by_contra vi;apply act;simp [θ,z,ind,live,val i vi]
    rw [ending] at hf
    obtain ⟨u,hu,_,_,eq⟩:=Clock.exists_head_poly hf
    have uz:u i=0:=by by_contra h;exact live ⟨u,hu,h⟩
    rw [eq i,uz,off,mul_zero,zero_add]
  obtain ⟨u,t,un,tn,tu,f,g⟩:=OrdinaryTrace.two_pivots_of_paid_clock (m:=2) ha ho tr tr.clock nz (by omega) (by omega) (by decide) (by decide) clean
  exact field _ ((RKCert.EndpointPhysical.quartic_physical_alternative P deg un tn tu f g).resolve_left nz)
end RKCert.Paired.Terminal
