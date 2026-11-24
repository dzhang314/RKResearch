module
public import RKCert.DirkRankBridge
public import RKCert.HeadChart

@[expose] public section
/-! # The true ambient even-order forward hidden carrier

This subspace is defined independently of the defect flag. An arbitrary
pure defect invisible on the two physical ports belongs to it; the
converse inclusion in any particular defect grade is not assumed.
There is one terminal compensation coordinate, not one free dimension.
-/
namespace RKCert.Paired.ERKEvenHidden
open RKCert.Paired RKCert.Paired.Clock Module Polynomial
open scoped Classical
variable {K:Type*} [Field K] {n:ℕ}
variable {b c d v:Vec K n} {g:Finset (Fin n)} {o t:Fin n}

def ambientHidden (b:Vec K n) (g:Finset (Fin n)) (t:Fin n) :
    Submodule K (Vec K n) where
  carrier := {v | (∀ i, i∉g → i≠t → v i=0) ∧ row b v=0}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv
    exact ⟨fun i h ht=>by simp only [Pi.add_apply,hu.1 i h ht,hv.1 i h ht,add_zero],
      by simp only [map_add,hu.2,hv.2,add_zero]⟩
  smul_mem' := by
    intro a u hu
    exact ⟨fun i h ht=>by simp only [Pi.smul_apply,hu.1 i h ht,smul_zero],
      by simp only [map_smul,hu.2,smul_zero]⟩

@[simp] theorem mem_ambientHidden :
    v∈ambientHidden b g t ↔ (∀ i, i∉g → i≠t → v i=0) ∧ row b v=0 := Iff.rfl

noncomputable def hiddenRestrict (b:Vec K n) (g:Finset (Fin n)) (t:Fin n) :
    ambientHidden b g t →ₗ[K] (g→K) :=
  LinearMap.pi (fun i:g=>(LinearMap.proj i.val).comp (ambientHidden b g t).subtype)

@[simp] theorem hiddenRestrict_apply (v:ambientHidden b g t) (i:g) :
    hiddenRestrict b g t v i=v.val i.val := rfl

theorem ambient_rank (ht:t∉g) (bt:b t≠0) : finrank K (ambientHidden b g t)=g.card := by
  classical
  have inj:Function.Injective (hiddenRestrict b g t) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro u hz
    have outside (i:Fin n) (hi:i≠t) : u.val i=0 := by
      by_cases ig:i∈g
      · have h:=congrFun hz (⟨i,ig⟩:g)
        simpa only [hiddenRestrict_apply,Pi.zero_apply] using h
      · exact (mem_ambientHidden.mp u.property).1 _ ig hi
    have mass:row b u.val=b t*u.val t := by
      rw [row_apply]
      exact Finset.sum_eq_single t (fun i _ hi=>by rw [outside i hi,mul_zero])
        (fun h=>False.elim (h (Finset.mem_univ t)))
    have zero:u.val t=0 :=
      (mul_eq_zero.mp (mass.symm.trans (mem_ambientHidden.mp u.property).2)).resolve_left bt
    apply Subtype.ext
    ext i
    by_cases hi:i=t
    · subst i;exact zero
    · exact outside _ hi
  have surj:Function.Surjective (hiddenRestrict b g t) := by
    intro x
    let w : Vec K n := fun i=>if hi:i∈g then x ⟨i,hi⟩ else 0
    let u : Vec K n := w-(row b w/b t)•Pi.single t 1
    have single : row b (Pi.single t 1)=b t := by simp [row_apply,Pi.single_apply]
    have hu:u∈ambientHidden b g t := by
      apply mem_ambientHidden.mpr
      refine ⟨fun i ni nt=>by simp [u,w,ni,Pi.single_eq_of_ne nt],?_⟩
      dsimp only [u]
      rw [map_sub,map_smul,smul_eq_mul,single,div_mul_cancel₀ _ bt,sub_self]
    refine ⟨⟨u,hu⟩,?_⟩
    ext i
    have away:i.val≠t := fun e=>ht (e ▸ i.property)
    simp only [hiddenRestrict_apply,u,w,Pi.sub_apply,Pi.smul_apply,i.property,dite_eq_left,
      Pi.single_eq_of_ne away,smul_zero,sub_zero,Subtype.coe_eta]
  have rank:finrank K (ambientHidden b g t)=finrank K (g→K) :=
    (LinearEquiv.ofBijective (hiddenRestrict b g t) ⟨inj,surj⟩).finrank_eq
  simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_coe] using rank

theorem ambient_invariant (fiber:∀i∈g,b i*(c i-c t)=0) :
    (ambientHidden b g t).map (diag c)≤ambientHidden b g t := by
  rintro _ ⟨u,hu,rfl⟩
  obtain ⟨outside,mass⟩:=mem_ambientHidden.mp hu
  apply mem_ambientHidden.mpr
  refine ⟨fun i hi ht=>by simp only [diag_apply,outside i hi ht,mul_zero],?_⟩
  have eq:row b (diag c u)=c t*row b u := by
    simp only [row_apply,diag_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi:i=t
    · subst i;ring
    by_cases hg:i∈g
    · linear_combination (u i)*(fiber i hg)
    · simp [outside i hg hi]
  rw [eq,mass,mul_zero]

noncomputable def activeRows (d:Vec K n) : Finset (Fin n) :=
  Finset.univ.filter (fun i=>d i≠0)

noncomputable def blindRows (c b d:Vec K n) (o t:Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i=>i≠o ∧ i≠t ∧ d i=0 ∧ (1-c i)*b i=0)

noncomputable abbrev carrier (c b d:Vec K n) (o t:Fin n) : Submodule K (Vec K n) :=
  ambientHidden b (blindRows c b d o t) t

@[simp] theorem mem_activeRows (i:Fin n) : i∈activeRows d ↔ d i≠0 := by simp [activeRows]
@[simp] theorem mem_blindRows (i:Fin n) :
    i∈blindRows c b d o t ↔ i≠o ∧ i≠t ∧ d i=0 ∧ (1-c i)*b i=0 := by
  simp [blindRows]

theorem carrier_rank (bt:b t≠0) : finrank K (carrier c b d o t)=(blindRows c b d o t).card :=
  ambient_rank (by simp) bt

theorem carrier_invariant (ct:c t=1) : (carrier c b d o t).map (diag c)≤carrier c b d o t := by
  apply ambient_invariant
  intro i hi
  rw [ct]
  linear_combination -((mem_blindRows i).mp hi).2.2.2

theorem carrier_of_no_visibility (org:v o=0) (mass:row b v=0)
    (d0:∀i,d i*v i=0) (b0:∀i,((1-c i)*b i)*v i=0) :
    v∈carrier c b d o t := by
  apply mem_ambientHidden.mpr
  refine ⟨fun i hi ht=>?_,mass⟩
  by_contra nv
  have no:i≠o := fun e=>nv (e ▸ org)
  have dd:d i=0 := (mul_eq_zero.mp (d0 i)).resolve_right nv
  have bb:(1-c i)*b i=0 := (mul_eq_zero.mp (b0 i)).resolve_right nv
  exact hi ((mem_blindRows i).mpr ⟨no,ht,dd,bb⟩)

theorem carrier_zero_on_active (ht:d t=0) (h:v∈carrier c b d o t)
    {i:Fin n} (hi:d i≠0) : v i=0 := by
  apply (mem_ambientHidden.mp h).1
  · exact fun hm=>hi ((mem_blindRows i).mp hm).2.2.1
  · exact fun eq=>hi (eq ▸ ht)

theorem carrier_mirror_weight_zero (ct:c t=1) (h:v∈carrier c b d o t)
    (i:Fin n) : ((1-c i)*b i)*v i=0 := by
  by_cases eq:i=t
  · subst i;simp [ct]
  by_cases hi:i∈blindRows c b d o t
  · rw [((mem_blindRows _).mp hi).2.2.2,zero_mul]
  · rw [(mem_ambientHidden.mp h).1 i hi eq,mul_zero]

theorem carrier_polynomial_separation {P:K[X]} (ht:d t=0)
    (sites:P.natDegree<(headSites c d).card)
    (h:(fun i=>P.eval (c i))∈carrier c b d o t) : P=0 := by
  classical
  apply eq_of_degrees_lt_of_eval_finset_eq (headSites c d)
  · exact degree_le_natDegree.trans_lt (by exact_mod_cast sites)
  · exact degree_le_natDegree.trans_lt (by
      rw [natDegree_zero];exact_mod_cast (show 0<(headSites c d).card by omega))
  · intro x hx
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
    rw [eval_zero]
    exact carrier_zero_on_active ht h (Finset.mem_filter.mp hi).2

/-- The disjoint physical budget behind the degree-two adjoint argument. -/
theorem carrier_contrast_budget {w:Vec K n} (bt:b t≠0) (dt:d t=0) (wt:w t=0)
    (ds:∀ i,d i≠0→w i=0) (gs:∀i∈blindRows c b d o t,w i=0) :
    finrank K (carrier c b d o t)+(activeRows d).card+(activeRows w).card+1≤n := by
  classical
  let G:=blindRows c b d o t
  let D:=activeRows d
  let W:=activeRows w
  have GD:Disjoint G D := Finset.disjoint_left.mpr fun i hi hd=>
    ((mem_activeRows i).mp hd) ((mem_blindRows i).mp hi).2.2.1
  have GW:Disjoint G W := Finset.disjoint_left.mpr fun i hi hw=>
    ((mem_activeRows i).mp hw) (gs i hi)
  have DW:Disjoint D W := Finset.disjoint_left.mpr fun i hd hw=>
    ((mem_activeRows i).mp hw) (ds i ((mem_activeRows i).mp hd))
  have J:Disjoint (G∪D) W := Finset.disjoint_union_left.mpr ⟨GW,DW⟩
  have tt:t∉(G∪D)∪W := by simp [G,D,W,dt,wt]
  have cnt:=Finset.card_le_univ (insert t ((G∪D)∪W))
  rw [Finset.card_insert_of_notMem tt,Finset.card_union_of_disjoint J,
    Finset.card_union_of_disjoint GD,Fintype.card_fin] at cnt
  rw [carrier_rank bt]
  change G.card+D.card+W.card+1≤n
  omega

theorem actual_defect_hidden {s p j:ℕ} {A:Fin (s+1)→Fin (s+1)→K}
    {b d v:Vec K (s+1)} (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    (pay:j+1≤p) (hv:v∈zeroSpace A j)
    (d0:∀i,d i*v i=0) (b0:∀i,((1-nodes A i)*b i)*v i=0) :
    v∈carrier (nodes A) b d 0 (Fin.last s) := by
  apply carrier_of_no_visibility (zeroSpace_first_of_row (fun i=>ha 0 i (Nat.zero_le _)) j hv) _ d0 b0
  have h:=probe_zeroSpace ho (k:=0) (by omega) hv
  change probe A b 0 v=0 at h
  simpa only [probe,pow_zero,mul_one] using h

end RKCert.Paired.ERKEvenHidden
