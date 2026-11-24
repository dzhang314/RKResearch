module
public import RKCert.DirkNineTwoHead
@[expose] public section
namespace RKCert.Paired.Terminal
open Module Polynomial RKCert.OneEscape
variable {K:Type*} [Field K] {s p:ℕ} {A:Fin s→Fin s→K} {b:Vec K s}
variable {U:Submodule K (Vec K s)} {w:Vec K s}

/-- Product localization needs only the actual products at issue, not
containment of *every* degree-ten pure column in the raised-nine space. -/
theorem core_mul_of_restricted_products {c:Vec K s} {n:ℕ} {B:Submodule K (Vec K s)}
    (inv:U.map (diag c)≤U) (norm:∀x,Clock.fiber c x w∈U→Clock.fiber c x w=0)
    (count:n<(Clock.headSites c w).card) (paid:∀v∈U,∀x∈B,v*x∈chain (diag c) U w n)
    {u x:Vec K s} (hu:u∈U) (hx:x∈B) : u*x∈U :=by
  classical
  have eqn:u*x=∑ z∈Clock.sites c, Clock.fiber c z u*x:=by rw [←Finset.sum_mul,Clock.sum_fibers]
  rw [eqn];apply U.sum_mem
  intro z _
  apply Clock.localized_mem (z:=z) inv norm count (paid _ (Clock.fiber_mem inv z hu) _ hx)
  intro i ne;simp [Clock.fiber,ne]

variable [CharZero K]
/-- Common order-19/order-20 r=2 finite-grade obstruction. Notably,
neither multiplicative closure of U, a disjoint head, a normalized
input, a global F₁₀ equality nor the quartic/primitive equations are
hypotheses. They are derived from the genuine restricted products. -/
theorem no_nine_two_head (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p) (hp:14≤p)
    (inv:U.map (diag (nodes A))≤U)
    (first:zeroSpace A 5=chain (diag (nodes A)) U w 2)
    (ninth:zeroSpace A 9=chain (diag (nodes A)) U w 6)
    (out:¬(raisedNine A).map (diag (nodes A))≤raisedNine A)
    (products:∀a∈zeroSpace A 5,∀v∈zeroSpace A 5,a*v∈raisedNine A) : False :=by
  classical
  let c:=nodes A
  let C:=diag c
  let w₀:=w-Clock.correction c U w
  have same (n:ℕ):chain C U w₀ n=chain C U w n:=
    chain_sub_head inv (Clock.correction_mem c U w) n
  have h5:zeroSpace A 5=chain C U w₀ 2:=first.trans (same 2).symm
  have hZ:raisedNine A=chain C U w₀ 7:=by
    rw [raisedNine,ninth.trans (same 6).symm,chain_sup_map inv (by decide:0<6)]
  have norm:∀z,Clock.fiber c z w₀∈U→Clock.fiber c z w₀=0:=Clock.normalized c U w
  have count:7<(Clock.headSites c w₀).card:=Clock.head_sites_of_noninvariant inv (by decide) (hZ ▸ out)
  have paid:=(chain_le_iff (T:=C) (U:=U) (w:=w₀) 2).mp h5.ge
  have keep (u:Vec K s) (hu:u∈U) (v:Vec K s) (hv:v∈zeroSpace A 5):u*v∈U:=
    core_mul_of_restricted_products inv norm count (fun x hx a ha=>hZ ▸ products x (paid.1 hx) a ha) hu hv
  have alg:Clock.MulClosed U:=fun x hx a ha=>keep x hx a (paid.1 ha)
  have w0:w₀∈zeroSpace A 5:=by simpa using paid.2 0 (by decide)
  obtain ⟨w',_,disj,e⟩:=Clock.disjoint_head inv alg (fun a ha=>keep a ha w₀ w0)
  exact no_disjoint_nine_two_head ha ho hp inv alg disj (h5.trans (e 2).symm) (hZ.trans (e 7).symm) out products
end RKCert.Paired.Terminal
