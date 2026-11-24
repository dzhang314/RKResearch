module
public import RKCert.ERKEvenHiddenCarrier
@[expose] public section
namespace RKCert.Paired.ERKOddHidden
open RKCert.Paired.ERKEvenHidden
variable {K:Type*} [Field K]
noncomputable section
theorem carrier_filler
    {s:ℕ}{c b d f:Vec K (s+1)} {o t:Fin (s+1)} (bt:b t≠0):
    ∃k∈carrier c b d o t,∀i∈blindRows c b d o t,k i=f i:=by
  classical
  let G:=blindRows c b d o t
  let u:Vec K (s+1):=fun i=>if i∈G then f i else 0
  let a:=row b u/b t
  let k:=u-a • Pi.single t 1
  have single:row b (Pi.single t (1:K))=b t:=by simp [row_apply,Pi.single_apply]
  refine ⟨k,mem_ambientHidden.mpr ⟨?_,?_⟩,?_⟩
  · intro i notG it
    change i∉G at notG
    simp [k,u,notG,Pi.single_eq_of_ne it]
  · rw [show k=u-a • Pi.single t 1 from rfl,map_sub,map_smul,smul_eq_mul,single,
      show a=row b u/b t from rfl,div_mul_cancel₀ _ bt,sub_self]
  · intro i hi
    have it:i≠t:=((mem_blindRows i).mp hi).2.1
    change i∈G at hi
    simp [k,u,hi,Pi.single_eq_of_ne it]

end
end RKCert.Paired.ERKOddHidden
