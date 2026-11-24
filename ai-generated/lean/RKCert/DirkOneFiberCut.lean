module
public import RKCert.DirkOverlappingHead
@[expose] public section
namespace RKCert.Paired.Clock
open Module Polynomial RKCert.OneEscape RKCert.Endpoint
variable {K:Type*} [Field K] {s:ℕ} {c:Vec K s} {V U:Submodule K (Vec K s)}
noncomputable section

theorem weightedEval_preserves (ui:U.map (diag c)≤U) (P:K[X]) {u:Vec K s} (hu:u∈U) :
    weightedEval c u P∈U:=by
  have e:weightedEval c u P=(fun i=>P.eval (c i)*u i):=funext (weightedEval_apply c u P)
  rw [e];exact poly_preserves ui P u hu

/-- The common invariant core after clearing at most one true clock fiber.
Away from its physical support, B(c) erases all contributions of the larger
core. This assertion does not ask for product closure of either starting core. -/
structure CoreCut (c:Vec K s) (V U:Submodule K (Vec K s)) where
  good:Submodule K (Vec K s)
  B:K[X]
  nz:B≠0
  deg:B.natDegree≤finrank K U-finrank K V
  inside:good≤V
  inv:good.map (diag c)≤good
  clear:∀u∈U,weightedEval c u B∈good
  keep:∀u∈good,∀v:Vec K s,u*v∈U→u*v∈good

/-- A codimension-one invariant quotient of a finite diagonal clock has at
most one exceptional numerical knot, even with repeated physical nodes. -/
theorem core_cut_of_codimension (inc:V≤U) (vi:V.map (diag c)≤V) (ui:U.map (diag c)≤U)
    (gap:finrank K U≤finrank K V+1) : Nonempty (CoreCut c V U):=by
  classical
  by_cases same:V=U
  · subst U
    refine ⟨⟨V,1,one_ne_zero,by simp,le_rfl,vi,?_,fun _ _ _ h=>h⟩⟩
    intro u hu
    have h:weightedEval c u 1=u:=by ext i;simp
    rwa [h]
  obtain ⟨v,hv,vout⟩:=IsConcreteLE.not_le_iff_exists.mp (fun a:U≤V=>same (le_antisymm inc a))
  have witness:∃a∈sites c,fiber c a v∉V:=by
    by_contra! neg
    apply vout
    rw [←sum_fibers c v]
    exact V.sum_mem (fun a ha=>neg a ha)
  obtain ⟨a,_,outside⟩:=witness
  let y:=fiber c a v
  have iy:y∈U:=fiber_mem ui a hv
  have full:V ⊔ Submodule.span K {y}=U:=Submodule.eq_of_le_of_finrank_le
    (sup_le inc ((Submodule.span_singleton_le_iff_mem ..).mpr iy))
    (by rw [Submodule.finrank_sup_span_singleton outside];exact gap)
  let G:Submodule K (Vec K s):={
    carrier:={u | u∈U ∧ ∀i,c i=a→u i=0}
    zero_mem':=⟨U.zero_mem,by simp⟩
    add_mem':=by rintro u v ⟨hu,uz⟩ ⟨hv,vz⟩; exact ⟨U.add_mem hu hv,fun i e=>by simp [uz i e,vz i e]⟩
    smul_mem':=by rintro t u ⟨hu,uz⟩;exact ⟨U.smul_mem t hu,fun i e=>by simp [uz i e]⟩ }
  have gin:G≤V:=by
    rintro u ⟨hu,uz⟩
    rw [←full] at hu
    obtain ⟨x,hx,k,hk,ex⟩:=Submodule.mem_sup.mp hu
    obtain ⟨t,rfl⟩:=Submodule.mem_span_singleton.mp hk
    have e:u=x-fiber c a x:=by
      ext i
      by_cases hit:c i=a
      · simp [uz i hit,fiber,hit]
      · simpa [y,fiber,hit] using (congrFun ex i).symm
    exact e ▸ V.sub_mem hx (fiber_mem vi a hx)
  refine ⟨⟨G,X-C a,X_sub_C_ne_zero a,?_,gin,?_,?_,?_⟩⟩
  · rw [natDegree_X_sub_C]
    have:=Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inc same);omega
  · rintro _ ⟨u,⟨hu,uz⟩,rfl⟩
    exact ⟨ui ⟨_,hu,rfl⟩,fun i e=>by change c i*u i=0;rw [uz i e,mul_zero]⟩
  · intro u hu
    exact ⟨weightedEval_preserves ui (X-C a) hu,fun i e=>by simp [e]⟩
  · rintro u ⟨_,uz⟩ v mem
    exact ⟨mem,fun i e=>by simp [Pi.mul_apply,uz i e]⟩

/-- Low-grade members of a fiber-cleared core absorb all genuine partners
whose product lands in a normalized complete late band. -/
theorem CoreCut.mixed {A:Fin s→Fin s→K} {w:Vec K s} {j k n:ℕ}
    (h:CoreCut (nodes A) V U) (vi:V≤zeroSpace A j) (ui:U.map (diag (nodes A))≤U)
    (norm:∀a,fiber (nodes A) a w∈U→fiber (nodes A) a w=0)
    (sites:n<(headSites (nodes A) w).card) (band:zeroSpace A (j+k)≤chain (diag (nodes A)) U w n)
    {u v:Vec K s} (hu:u∈h.good) (hv:v∈zeroSpace A k):u*v∈h.good:=by
  classical
  apply h.keep u hu v
  rw [←sum_fibers (nodes A) u,Finset.sum_mul]
  apply U.sum_mem
  intro z _
  apply localized_mem (z:=z) ui norm sites (band (zeroSpace_mul (vi (h.inside (fiber_mem h.inv z hu))) hv))
  intro i ne
  simp [fiber,ne]
end
end RKCert.Paired.Clock

