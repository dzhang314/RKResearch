module
public import RKCert.ERKOddBlockPayment
public import RKCert.ClockMaskAlgebra
public import RKCert.CoreSupport

@[expose] public section
/-! # Original forward algebra labels and true reverse block sums -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.ClockClass Module
open scoped Classical
variable {K:Type*} [Field K] {s:ℕ}
noncomputable section

def forwardValueTag (U:Submodule K (Vec K s))(i:Fin s):U→K:=fun v=>v.val i

theorem forwardValueTag_iff {U:Submodule K (Vec K s)} {i j:Fin s}:
    forwardValueTag U i=forwardValueTag U j↔SameClass U i j:=by
  constructor
  · intro h v hv
    exact congrFun h (⟨v,hv⟩:U)
  · intro h
    funext x
    exact h _ x.property

theorem forwardValueTag_zero {U:Submodule K (Vec K s)} {i:Fin s}:
    forwardValueTag U i=0↔¬Clock.Live U i:=by
  constructor
  · rintro e ⟨u,hu,z⟩
    exact z (congrFun e (⟨u,hu⟩:U))
  · intro h
    funext u
    change u.val i=0
    by_contra z
    exact h ⟨_,u.property,z⟩

theorem forward_value_classes_rank (U:Submodule K (Vec K s)):
    finrank K U≤((Finset.univ.filter (fun i:Fin s=>Clock.Live U i)).image (forwardValueTag U)).card:=by
  let S:Finset (U→K):=(Finset.univ.filter (fun i:Fin s=>Clock.Live U i)).image (forwardValueTag U)
  have ex(a:S):∃i:Fin s,forwardValueTag U i=a.val:=by
    obtain ⟨i,_,e⟩:=Finset.mem_image.mp a.property
    exact ⟨i,e⟩
  let r(a:S):=Classical.choose (ex a)
  have rr(a:S):forwardValueTag U (r a)=a.val:=Classical.choose_spec (ex a)
  let E:U→ₗ[K](S→K):=LinearMap.pi (fun a=>(LinearMap.proj (r a)).comp U.subtype)
  have inj:Function.Injective E:=by
    intro v w h
    apply Subtype.ext
    ext i
    by_cases live:Clock.Live U i
    · let j:S:=⟨forwardValueTag U i,Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,live⟩,rfl⟩⟩
      have h0:=congrFun h j
      change v.val (r j)=w.val (r j) at h0
      have same:SameClass U (r j) i:=forwardValueTag_iff.mp (rr j)
      rwa [same _ v.property,same _ w.property] at h0
    · have a:v.val i=0:=by by_contra nz;exact live ⟨v.val,v.property,nz⟩
      have b:w.val i=0:=by by_contra nz;exact live ⟨w.val,w.property,nz⟩
      rw [a,b]
  have p:=LinearMap.finrank_le_finrank_of_injective inj
  rwa [Module.finrank_fintype_fun_eq_card,Fintype.card_coe] at p

theorem class_restrict_preserves
    {G U:Submodule K (Vec K s)} (alg:Clock.MulClosed G)
    (mul:∀g∈G,∀u∈U,g*u∈U) {v:Vec K s}(vu:v∈U)(i:Fin s):
    (fun j=>if forwardValueTag G j=forwardValueTag G i then v j else 0)∈U:=by
  by_cases live:Clock.Live G i
  · have mem:=classIndicator_mem alg i live
    have p:=mul _ mem v vu
    have e:classIndicator G i*v=(fun j=>if forwardValueTag G j=forwardValueTag G i then v j else 0):=by
      ext j
      rw [Pi.mul_apply,classIndicator_at]
      by_cases h:SameClass G i j
      · have t:forwardValueTag G j=forwardValueTag G i:=(forwardValueTag_iff.mpr h).symm
        simp [h,t]
      · have t:forwardValueTag G j≠forwardValueTag G i:=fun t=>h (forwardValueTag_iff.mp t.symm)
        simp [h,t]
    rwa [e] at p
  obtain ⟨e,eG,atRow⟩:=core_indicator alg
  have c0:forwardValueTag G i=0:=forwardValueTag_zero.mpr live
  have eq:v-e*v=(fun j=>if forwardValueTag G j=forwardValueTag G i then v j else 0):=by
    ext j
    by_cases h:Clock.Live G j
    · have g:forwardValueTag G j≠0:=fun z=>(forwardValueTag_zero.mp z) h
      simp [Pi.sub_apply,Pi.mul_apply,atRow,c0,g,h]
    · have g:forwardValueTag G j=0:=forwardValueTag_zero.mpr h
      simp [Pi.sub_apply,Pi.mul_apply,atRow,c0,g,h]
  rw [←eq]
  exact U.sub_mem vu (mul _ eG _ vu)

def taggedPhysicalBlock (G:Submodule K (Vec K s))(c f g:Vec K s)(i:Fin s):
    K×K×K×(G→K):=(c i,f i,g i,forwardValueTag G i)

theorem tagged_blocks_zero_on_base
    {G U:Submodule K (Vec K s)} {c f g:Vec K s}
    (alg:Clock.MulClosed G)(mul:∀h∈G,∀u∈U,h*u∈U)
    (ci:U.map (diag c)≤U)(fi:U.map (diag f)≤U)(gi:U.map (diag g)≤U)
    (zero:∀u∈U,(∑i,u i)=0):
    U≤(blockTotal (taggedPhysicalBlock G c f g)).ker:=by
  classical
  let : DecidableEq (K×K×K×(G→K)):=Classical.decEq _
  intro u hu
  change blockTotal (taggedPhysicalBlock G c f g) u=0
  funext a
  obtain ⟨i,_,ai⟩:=Finset.mem_image.mp a.property
  let v:Vec K s:=fun j=>if forwardValueTag G j=forwardValueTag G i then u j else 0
  have vu:v∈U:=class_restrict_preserves alg mul hu i
  let w:=fiber c (c i) (fiber f (f i) (fiber g (g i) v))
  have ww:w∈U:=fiber_mem ci _ (fiber_mem fi _ (fiber_mem gi _ vu))
  have z:=zero w ww
  rw [blockTotal_apply,Finset.sum_filter,Pi.zero_apply]
  convert z using 1
  apply Finset.sum_congr rfl
  intro j _
  rw [←ai]
  by_cases h:c j=c i <;> by_cases e:f j=f i <;> by_cases l:g j=g i <;>
    by_cases k:forwardValueTag G j=forwardValueTag G i <;>
    simp [taggedPhysicalBlock,w,v,fiber,h,e,l,k]
end
end RKCert.Paired.ReverseHull

