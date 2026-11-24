module

public import RKCert.ReviewedNative.ReversePaidTraces
public import RKCert.ReviewedNative.NativePrimitiveMoments

@[expose] public section

/-! # Actual compensated hidden support, not a quotient by fictitious rows

A vector supported on the physical blind rows and the last coordinate,
and of zero output mass, is a genuine forward defect if the terminal
deleted reverse flag covers precisely the paid quadratic support.
The endpoint moment argument is valid in characteristic zero without
sign assumptions on the weights or abscissae. -/
namespace RKResearch.Certified.Graded.Reverse.Hidden
open RKResearch Polynomial Module RKCert.Endpoint RKCert.Endpoint.WeightedClock
open NativeMoments
open scoped Classical Matrix

noncomputable section
variable {K : Type*} [Field K] {n : ℕ}
variable {b c d v : Fin n→K} {g : Finset (Fin n)} {o t : Fin n}
set_option maxRecDepth 3500
set_option maxHeartbeats 800000

def ambientHidden (b:(Fin n→K)) (g:Finset (Fin n)) (t:Fin n) :
    Submodule K ((Fin n→K)) where
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

noncomputable def hiddenRestrict (b:(Fin n→K)) (g:Finset (Fin n)) (t:Fin n) :
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
      rw [row_apply,dotProduct]
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
    let w : (Fin n→K) := fun i=>if hi:i∈g then x ⟨i,hi⟩ else 0
    let u : (Fin n→K) := w-(row b w/b t)•Pi.single t 1
    have single : row b (Pi.single t 1)=b t := by simp [dotProduct,Pi.single_apply]
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
    simp only [row_apply,dotProduct,diag_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi:i=t
    · subst i;ring
    by_cases hg:i∈g
    · linear_combination (u i)*(fiber i hg)
    · simp [outside i hg hi]
  rw [eq,mass,mul_zero]

noncomputable def activeRows (d:(Fin n→K)) : Finset (Fin n) :=
  Finset.univ.filter (fun i=>d i≠0)

noncomputable def blindRows (c b d:(Fin n→K)) (o t:Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i=>i≠o ∧ i≠t ∧ d i=0 ∧ (1-c i)*b i=0)

noncomputable abbrev carrier (c b d:(Fin n→K)) (o t:Fin n) : Submodule K ((Fin n→K)) :=
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
    (sites:P.natDegree<(weightedSites c d).card)
    (h:(fun i=>P.eval (c i))∈carrier c b d o t) : P=0 := by
  classical
  apply eq_of_degrees_lt_of_eval_finset_eq (weightedSites c d)
  · exact degree_le_natDegree.trans_lt (by exact_mod_cast sites)
  · exact degree_le_natDegree.trans_lt (by
      rw [natDegree_zero];exact_mod_cast (show 0<(weightedSites c d).card by omega))
  · intro x hx
    obtain ⟨i,hi,rfl⟩:=mem_weightedSites.mp hx
    rw [eval_zero]
    exact carrier_zero_on_active ht h hi

/-- The disjoint physical budget behind the degree-two adjoint argument. -/
theorem carrier_contrast_budget {w:(Fin n→K)} (bt:b t≠0) (dt:d t=0) (wt:w t=0)
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
    {b d v:(Fin (s+1)→K)} (ha : ∀ i j, i≤j → A i j=0) (ho:HasOrder p A b)
    (pay:j+1≤p) (hv:v∈zeroSpace A j)
    (d0:∀i,d i*v i=0) (b0:∀i,((1-nodes A i)*b i)*v i=0) :
    v∈carrier (nodes A) b d 0 (Fin.last s) := by
  apply carrier_of_no_visibility (origin_zeroSpace ha j hv) _ d0 b0
  have h:=probe_zeroSpace ho (k:=0) (by omega) hv
  change probe A b 0 v=0 at h
  simpa only [probe,pow_zero,mul_one] using h

theorem carrier_filler
    {s:ℕ}{c b d f:(Fin (s+1)→K)} {o t:Fin (s+1)} (bt:b t≠0):
    ∃k∈carrier c b d o t,∀i∈blindRows c b d o t,k i=f i:=by
  classical
  let G:=blindRows c b d o t
  let u:(Fin (s+1)→K):=fun i=>if i∈G then f i else 0
  let a:=row b u/b t
  let k:=u-a • Pi.single t 1
  have single:row b (Pi.single t (1:K))=b t:=by simp [dotProduct,Pi.single_apply]
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

section Actual

variable [CharZero K] {s p q : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {w : Fin (s+1) → K}

/-- The terminal compensated physical support falls inside the true
unmarked degree-q defect span, not just the marked tree span. -/
theorem carrier_le_defects (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder p A w)
    (paid : 2*q+1≤p) (ct : nodes A (Fin.last s)=1) (bt : w (Fin.last s)≠0)
    (dt : quadraticSeed A w (Fin.last s)=0)
    (support : Thin.SupportsComplement A w q (Fin.last s)) :
    carrier (nodes A) w (quadraticSeed A w) 0 (Fin.last s)≤zeroSpace A q := by
  classical
  let t := Fin.last s
  let e := coordinate (K:=K) t
  let d := quadraticSeed A w
  let U := carrier (nodes A) w d 0 t
  have c0 : nodes A 0=0 := by
    change (∑ i, A 0 i * (1 : K))=0
    exact Finset.sum_eq_zero fun i _ => by rw [ha 0 i (Fin.zero_le i),zero_mul]
  have t0 : t≠0 := by intro z; exact zero_ne_one (c0.symm.trans (z ▸ ct))
  intro f hf
  obtain ⟨off,mass⟩ := mem_ambientHidden.mp hf
  have f0 : f 0=0 := off 0 (fun h => ((mem_blindRows 0).mp h).1 rfl) (Ne.symm t0)
  have mix : f∈treeSpace A q ⊔ K ∙ e := by
    rw [←annih_annih (treeSpace A q ⊔ K ∙ e),
      show annih (treeSpace A q ⊔ K ∙ e)=zeroAt (annih (treeSpace A q)) t from
        annih_sup_coordinate _ t]
    apply mem_annih.mpr
    intro u hu
    rw [row_apply,dotProduct]
    apply Finset.sum_eq_zero
    intro i _
    by_cases di : d i=0
    · rw [support u hu i di,mul_zero]
    · rw [carrier_zero_on_active dt hf di,zero_mul]
  obtain ⟨f',hf',u,hu,rfl⟩ := Submodule.mem_sup.mp mix
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hu
  have f'0 : f' 0=0 := by
    have e0 : e 0=0 := by
      unfold e coordinate
      exact @Pi.single_eq_of_ne (Fin (s+1)) (fun _ => K) _ (Classical.decEq _) t 0 (Ne.symm t0) 1
    change f' 0+a*e 0=0 at f0
    rwa [e0,mul_zero,add_zero] at f0
  rw [treeSpace_coeff_sup ho (by omega : q+1≤p)] at hf'
  obtain ⟨u,hu,z,hz,huz⟩ := Submodule.mem_sup.mp hf'
  obtain ⟨coef,rfl⟩ := hu
  let P : K[X] := ofFn (q+1) coef
  have deg : P.natDegree≤q := by
    change (ofFn (q+1) coef).natDegree≤q
    have h := ofFn_natDegree_lt (by omega : 0<q+1) coef
    omega
  have ep : evalNodes A P=coeffEval A q coef := by
    rw [evalNodes_eq_coeffEval A P deg]
    congr 1
    exact toFn_comp_ofFn_eq_id _ _
  have tr : f'-evalNodes A P∈zeroSpace A q := by
    rw [←huz,ep,add_sub_cancel_left]
    exact hz
  have P0 : P.eval 0=0 := by
    have z := origin_zeroSpace ha q tr
    change f' 0-P.eval (nodes A 0)=0 at z
    rw [f'0,c0,zero_sub,neg_eq_zero] at z
    exact z
  have wzero (i : Fin (s+1)) : ((1-nodes A i)*w i)*f' i=0 := by
    have h := carrier_mirror_weight_zero ct hf i
    by_cases eq : i=t
    · subst i; rw [ct,sub_self,zero_mul,zero_mul]
    · have ei : e i=0 := by
        unfold e coordinate
        exact @Pi.single_eq_of_ne (Fin (s+1)) (fun _ => K) _ (Classical.decEq _) t i eq 1
      change ((1-nodes A i)*w i)*(f' i+a*e i)=0 at h
      rwa [ei,mul_zero,add_zero] at h
  have probeZ (i : Fin q) : reflectedProbe A w i.val 1 f'=0 := by
    simp only [reflectedProbe,row_apply,dotProduct,pow_one]
    apply Finset.sum_eq_zero
    intro j _
    change (w j * nodes A j^i.val * (1-nodes A j))*f' j=0
    rw [show (w j * nodes A j^i.val * (1-nodes A j))*f' j=
      nodes A j^i.val * (((1-nodes A j)*w j)*f' j) by ring,wzero,mul_zero]
  have Pz : P=0 := endpoint_moments_detect deg P0 (fun i => by
    have h := reflectedProbe_primitive_of_defect ho i.val 1 (by have := i.isLt; omega) deg tr
    simpa only [probeZ i,pow_one] using h.symm)
  have defect : f'∈zeroSpace A q := by simpa only [Pz,map_zero,sub_zero] using tr
  have mass' : row w f'=0 := by
    have z := probe_zeroSpace ho (k:=0) (by omega) defect
    change probe A w 0 f'=0 at z
    simpa only [probe,pow_zero,mul_one] using z
  rw [map_add,map_smul,smul_eq_mul,mass',show row w e=w t from row_coordinate w t,zero_add] at mass
  have az := (mul_eq_zero.mp mass).resolve_right bt
  simpa only [az,zero_smul,add_zero] using defect

end Actual
end
end RKResearch.Certified.Graded.Reverse.Hidden
