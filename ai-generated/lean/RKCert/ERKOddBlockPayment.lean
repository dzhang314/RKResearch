module
public import RKCert.ERKOddLocalOrthogonal

@[expose] public section
/-! # Signed physical block payments by one true restriction map
The dimension debit of the reverse base and of independently paid
zero-sum directions is separate from the number of nonempty physical
blocks. No artificial reduced tableau is used. -/
namespace RKCert.Paired.ReverseHull
open Module
open scoped Classical
variable {K L:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s:ℕ}
noncomputable section

def physicalBlocks (c:Fin s→L):Finset L:=Finset.univ.image c

theorem site_block_mem (c:Fin s→L)(i:Fin s):c i∈physicalBlocks c:=
  Finset.mem_image_of_mem _ (Finset.mem_univ _)

def blockTotal (c:Fin s→L) : Vec K s→ₗ[K](physicalBlocks c→K):=
  LinearMap.pi (fun a=>∑ i ∈ Finset.univ.filter (fun i=>c i=a.val),LinearMap.proj i)

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem blockTotal_apply (c:Fin s→L)(x:Vec K s)(a:physicalBlocks c):
    blockTotal c x a=∑ i ∈ Finset.univ.filter (fun i=>c i=a.val),x i:=by
  simp [blockTotal]

theorem blockTotal_surjective (c:Fin s→L) : Function.Surjective (blockTotal (K:=K) c):=by
  classical
  intro f
  let D(a:L):Finset (Fin s):=Finset.univ.filter (fun i=>c i=a)
  let v:Vec K s:=fun i=>f ⟨c i,site_block_mem c i⟩/(D (c i)).card
  refine ⟨v,?_⟩
  funext a
  have nz:((D a.val).card:K)≠0:=by
    apply Nat.cast_ne_zero.mpr
    obtain ⟨i,_,e⟩:=Finset.mem_image.mp a.property
    exact Finset.card_ne_zero.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,e⟩⟩
  rw [blockTotal_apply]
  change (∑ i ∈ D a.val,v i)=f a
  calc
    _=∑ i ∈ D a.val,f a/((D a.val).card:K):=by
      apply Finset.sum_congr rfl
      intro i ig
      have same:c i=a.val:=(Finset.mem_filter.mp ig).2
      have q:(⟨c i,site_block_mem c i⟩:physicalBlocks c)=a:=Subtype.ext same
      rw [show v i=f ⟨c i,site_block_mem c i⟩/(D (c i)).card from rfl,q,same]
    _=f a:=by
      rw [Finset.sum_const,nsmul_eq_mul]
      field_simp [nz]

theorem rank_with_physical_blocks (c:Fin s→L)
    (U W:Submodule K (Vec K s))
    (u0:U≤(blockTotal c).ker)(w0:W≤(blockTotal c).ker)(orth:W≤annih U):
    finrank K U+finrank K W+(physicalBlocks c).card≤s:=by
  have inter:U⊓W=⊥:=by
    apply le_bot_iff.mp
    rintro v ⟨u,w⟩
    exact dot_orthogonal_inter_zero u (orth w)
  have d:=Submodule.finrank_sup_add_finrank_inf_eq U W
  rw [inter,finrank_bot,add_zero] at d
  have b:=Submodule.finrank_mono (sup_le u0 w0)
  have r:=(blockTotal (K:=K) c).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (blockTotal_surjective c),finrank_top,Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe,Module.finrank_fin_fun] at r
  omega

end
end RKCert.Paired.ReverseHull

