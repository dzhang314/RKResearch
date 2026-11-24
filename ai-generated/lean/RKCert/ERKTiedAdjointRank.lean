module
public import RKCert.ERKTiedReverseRows

@[expose] public section
/-! # Tied reverse rank closure without a projected reverse hull -/
namespace RKCert.Paired
open RKCert.Paired.OrderTwelve Module
variable {K:Type*} [Field K] [CharZero K]
variable {A:Fin 17→Fin 17→K} {b:Vec K 17}
set_option maxHeartbeats 3000000

omit [CharZero K] in
private theorem annih_next_of_clock_pair {j:ℕ} {x:Vec K 17}
    (step:treeSpace A (j+1)=treeSpace A j⊔(treeSpace A j).map (diag (mirror A)))
    (x0:x∈annih (treeSpace A j)) (x1:diag (mirror A) x∈annih (treeSpace A j)) :
    x∈annih (treeSpace A (j+1)) := by
  apply mem_annih.mpr
  intro v hv
  rw [step] at hv
  obtain ⟨u,hu,z,⟨w,hw,rfl⟩,rfl⟩:=Submodule.mem_sup.mp hv
  change row x (u+diag (mirror A) w)=0
  rw [map_add,←row_flip_diag,mem_annih.mp x0 _ hu,mem_annih.mp x1 _ hw,add_zero]

omit [CharZero K] in
private theorem zero_after_full {x:Vec K 17} (hfull:treeSpace A 10=⊤)
    (hx:x∈annih (treeSpace A 10)) : x=0 := by
  ext i
  have hi : (Pi.single i (1:K))∈treeSpace A 10 := by rw [hfull];trivial
  have e:=mem_annih.mp hx _ hi
  simpa [row_apply,Pi.single_apply] using e

/-- If a 17-stage partial shadow has the paid forward flag and its first
adjoint is live at the last nonzero output, the source order-thirteen
reflected rows alone force contradiction. -/
theorem tied_reverse_contradiction_of_ranks (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 11)
    (r7:finrank K (treeSpace A 7)=14) (r8:finrank K (treeSpace A 8)=15)
    (r9:finrank K (treeSpace A 9)=16) (r10:finrank K (treeSpace A 10)=17)
    (step8:treeSpace A 9=treeSpace A 8⊔(treeSpace A 8).map (diag (mirror A)))
    (step9:treeSpace A 10=treeSpace A 9⊔(treeSpace A 9).map (diag (mirror A)))
    (ell2:reverseResidual A b 1∈annih (treeSpace A 9))
    (ell3:reverseResidual A b 2∈annih (treeSpace A 9))
    (ell4:reverseResidual A b 3∈annih (treeSpace A 8))
    (first:∃ i:Fin 17,(∀ j,i<j→b j=0)∧reverseResidual A b 0 i≠0) : False := by
  obtain ⟨i,later,piv⟩:=first
  let d:=reverseResidual A b 0
  let Y:=diag (mirror A)
  let N:=transMat A
  let L1 : Submodule K (Vec K 17) := K ∙ d
  let L2 : Submodule K (Vec K 17) := L1 ⊔ (K ∙ Y d)
  let L3 : Submodule K (Vec K 17) := L2 ⊔ (K ∙ Y (Y d))
  have dn:d≠0:=by intro h;exact piv (by change d i=0;rw [h,Pi.zero_apply])
  have d9 : d∈annih (treeSpace A 9) := reverseResidual_mem ho (by decide) (by decide)
  have Y8 {j:ℕ} {x:Vec K 17} (hx:x∈annih (treeSpace A (j+1))) :
      Y x∈annih (treeSpace A j) := by
    apply mem_annih.mpr
    intro v hv
    rw [show Y=diag (mirror A) from rfl,row_flip_diag]
    exact mem_annih.mp hx _ (mirror_treeSpace A j hv)
  have N8 {j:ℕ} {x:Vec K 17} (hx:x∈annih (treeSpace A (j+1))) :
      N x∈annih (treeSpace A j) := by
    apply mem_annih.mpr
    intro v hv
    rw [show N=transMat A from rfl,row_flip_mat]
    exact mem_annih.mp hx _ (mat_treeSpace A j hv)
  have y8 : Y d∈annih (treeSpace A 8) := Y8 d9
  have yy7 : Y (Y d)∈annih (treeSpace A 7) := Y8 y8
  have full : treeSpace A 10=⊤ := Submodule.eq_top_of_finrank_eq (by simpa only [Module.finrank_fin_fun] using r10)
  have y9n : Y d∉annih (treeSpace A 9) := fun hy=>dn (zero_after_full full (annih_next_of_clock_pair step9 d9 hy))
  have yy8n : Y (Y d)∉annih (treeSpace A 8) :=
    fun hy=> y9n (annih_next_of_clock_pair step8 y8 hy)
  have rank1 := finrank_annih_le (U:=treeSpace A 9) (V:=annih (treeSpace A 9)) le_rfl
  have rank2 := finrank_annih_le (U:=treeSpace A 8) (V:=annih (treeSpace A 8)) le_rfl
  have rank3 := finrank_annih_le (U:=treeSpace A 7) (V:=annih (treeSpace A 7)) le_rfl
  have L1le : L1≤annih (treeSpace A 9) := (Submodule.span_singleton_le_iff_mem ..).mpr d9
  have L2le : L2≤annih (treeSpace A 8) := sup_le
    (L1le.trans (by intro x hx;exact mem_annih.mpr (fun v hv=>mem_annih.mp hx v (treeSpace_mono A (by decide : 8≤9) hv))))
    ((Submodule.span_singleton_le_iff_mem ..).mpr y8)
  have L3le : L3≤annih (treeSpace A 7) := sup_le
    (L2le.trans (by intro x hx;exact mem_annih.mpr (fun v hv=>mem_annih.mp hx v (treeSpace_mono A (by decide : 7≤8) hv))))
    ((Submodule.span_singleton_le_iff_mem ..).mpr yy7)
  have s1 : finrank K L1=1 := finrank_span_singleton dn
  have s2 : finrank K L2=2 := by
    change finrank K ↥(L1 ⊔ (K ∙ (Y d)))=2
    rw [Submodule.finrank_sup_span_singleton (fun hy=>y9n (L1le hy)),s1]
  have s3 : finrank K L3=3 := by
    change finrank K ↥(L2 ⊔ (K ∙ (Y (Y d))))=3
    rw [Submodule.finrank_sup_span_singleton (fun hy=>yy8n (L2le hy)),s2]
  have e1 : L1=annih (treeSpace A 9) := Submodule.eq_of_le_of_finrank_le L1le (by omega)
  have e2 : L2=annih (treeSpace A 8) := Submodule.eq_of_le_of_finrank_le L2le (by omega)
  have e3 : L3=annih (treeSpace A 7) := Submodule.eq_of_le_of_finrank_le L3le (by omega)
  have single {v:Vec K 17} (hv:v∈annih (treeSpace A 9)) :
      ∃ a:K,∀j,v j=a*d j := by
    rw [←e1] at hv
    obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp hv
    exact ⟨a,fun j=>by simp⟩
  have pair {v:Vec K 17} (hv:v∈L2) :
      ∃ a c:K,∀j,v j=(a+c*mirror A j)*d j := by
    obtain ⟨x,hx,z,hz,rfl⟩:=Submodule.mem_sup.mp hv
    obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp hx
    obtain ⟨c,rfl⟩:=Submodule.mem_span_singleton.mp hz
    exact ⟨a,c,fun j=>by simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Y,diag_apply];ring⟩
  have triple {v:Vec K 17} (hv:v∈L3) :
      ∃ a c f:K,∀j,v j=(a+c*mirror A j+f*(mirror A j)^2)*d j := by
    obtain ⟨x,hx,z,hz,rfl⟩:=Submodule.mem_sup.mp hv
    obtain ⟨a,c,eq⟩:=pair hx
    obtain ⟨f,rfl⟩:=Submodule.mem_span_singleton.mp hz
    exact ⟨a,c,f,fun j=>by simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Y,diag_apply,eq];ring⟩
  have αn : reverseResidual A b 1 i≠0 := tied_second_nonzero_at_pivot ha later piv
  obtain ⟨α,αe⟩:=single ell2
  have αne : α≠0 := fun he=> αn (by rw [αe,he,zero_mul])
  exact tied_adjoint_profile_impossible ha ho (by decide) ⟨α,αne,αe⟩ (single ell3)
    (pair (e2.symm ▸ ell4)) (pair (e2.symm ▸ N8 d9)) (triple (e3.symm ▸ N8 y8))

end RKCert.Paired
