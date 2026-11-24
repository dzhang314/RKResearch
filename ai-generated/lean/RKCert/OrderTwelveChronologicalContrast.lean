module
public import RKCert.OrderTwelveMultiplierProfile
public import RKCert.ERKPhysicalContrasts

@[expose] public section
namespace RKCert.Paired.OrderTwelve
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint Polynomial
variable {K:Type*} [Field K] [CharZero K]
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {r:ℕ} {U:Submodule K (Vec K (s+1))} {w v:Vec K (s+1)}

/-- Code the finite simultaneous clock/multiplier classes as elements of the
field. The code is used only for comparing equality, not as a clock. -/
theorem joint_labels {c v:Vec K (s+1)} (hc:U.map (diag c)≤U) (hv:U.map (diag v)≤U) :
    ∃ label:Vec K (s+1), (∀ i j,label i=label j↔c i=c j ∧ v i=v j) ∧ MaskInvariant label U := by
  classical
  let T := Finset.univ.image (fun j:Fin (s+1)=>(c j,v j))
  let jT (j:Fin (s+1)) : T := ⟨(c j,v j),Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  let f := Fintype.equivFin T
  let label : Vec K (s+1):= fun j=>((f (jT j)).val:K)
  have eq (i j:Fin (s+1)):label i=label j↔c i=c j ∧ v i=v j := by
    constructor
    · intro h
      have he : jT i=jT j := f.injective (Fin.ext (Nat.cast_injective h))
      have e : (c i,v i)=(c j,v j) := congrArg Subtype.val he
      exact ⟨congrArg Prod.fst e,congrArg Prod.snd e⟩
    · rintro ⟨e₁,e₂⟩
      have h : jT i=jT j := Subtype.ext (Prod.ext e₁ e₂)
      simp [label,h]
  refine ⟨label,eq,?_⟩
  intro x a ha
  by_cases h:∃ j,label j=x
  · obtain ⟨i,rfl⟩:=h
    have ep : blockMask label (label i) a=fiber v (v i) (fiber c (c i) a) := by
      ext j
      by_cases e₁:c j=c i <;> by_cases e₂:v j=v i <;>
        simp [blockMask,fiber,eq j i,e₁,e₂]
    rw [ep]
    exact fiber_mem hv _ (fiber_mem hc _ ha)
  · have hz : blockMask label x a=0 := by
      ext j
      have h' : label j≠x := fun e=>h ⟨j,e⟩
      simp [blockMask,h']
    rw [hz];exact U.zero_mem

omit [CharZero K] in
theorem stage_weighted_grade (ho:HasTreeOrderAtLeast A b 12) (R:K[X]) {j:ℕ}
    (hR:R.natDegree+1≤12) (hv:v∈zeroSpace A j) :
    weightedEval (nodes A) v R∈zeroSpace A (j+R.natDegree) := by
  have e : weightedEval (nodes A) v R=v*evalNodes A R := by
    ext j
    simp [weightedEval_apply,evalNodes,mul_comm]
  rw [e]
  exact zeroSpace_mul_treeSpace ho hR hv (evalNodes_mem_treeSpace A R le_rfl)

noncomputable def evalForm (A:Fin (s+1)→Fin (s+1)→K) : K[X] →ₗ[K] Vec K (s+1) :=
  LinearMap.pi (fun j=>Polynomial.leval (nodes A j))

noncomputable def contrastResidual (A:Fin (s+1)→Fin (s+1)→K) (v:Vec K (s+1)) (P:K[X]) :
    K[X] →ₗ[K] Vec K (s+1) :=
  let rp : K[X] →ₗ[K] K[X] :=
    { toFun := fun R=>R*P
      map_add' := fun a b=>add_mul a b P
      map_smul' := fun a b=>smul_mul_assoc a b P }
  (evalForm A).comp (Paired.primitive.comp rp) -
    (mat A).comp ((evalForm A).comp rp-weightedEval (nodes A) v)

omit [CharZero K] in
theorem contrastResidual_apply (P R:K[X]) :
    contrastResidual A v P R=evalNodes A (Paired.primitive (R*P))-
      mat A (evalNodes A (R*P)-weightedEval (nodes A) v R) := rfl

theorem contrast_residual_grade (P R:K[X]) {q:ℕ} (hp:(R*P).natDegree≤q)
    (hv:weightedEval (nodes A) v R∈zeroSpace A q) :
    contrastResidual A v P R∈zeroSpace A (q+1) := by
  rw [contrastResidual_apply,map_sub,sub_sub_eq_add_sub]
  have e : evalNodes A (Paired.primitive (R*P))+mat A (weightedEval (nodes A) v R)-
      mat A (evalNodes A (R*P)) = -(mat A (evalNodes A (R*P))-
      evalNodes A (Paired.primitive (R*P)))+mat A (weightedEval (nodes A) v R) := by abel
  rw [e]
  exact (zeroSpace A (q+1)).add_mem ((zeroSpace A (q+1)).neg_mem (primitive_defect A _ hp))
    (mat_zeroSpace_charZero A _ hv)

theorem cubic_single_leak (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    (hs:Saturation A b) (hi:b (Fin.last s)≠0)
    (P:K[X]) (dp:P.natDegree≤3)
    (cheap:∀ R:K[X],R.natDegree≤2→weightedEval (nodes A) v R∈zeroSpace A 5)
    (high:weightedEval (nodes A) v (X^3)∈zeroSpace A 6) :
    ∃ α:K, ∀ R:K[X],R.natDegree≤3→
      contrastResidual A v P R-(α*R.coeff 3) • evalNodes A ghost7∈escape7 A := by
  have no : ∀ j:Fin (s+1),Fin.last s<j→b j=0 := fun j h=>False.elim ((not_lt_of_ge (Fin.le_last j)) h)
  have h3 : contrastResidual A v P (X^3)∈zeroSpace A 7 :=
    contrast_residual_grade _ _ ((natDegree_mul_le).trans (by rw [natDegree_X_pow];omega)) high
  obtain ⟨α,eq⟩:=ghost7_leak ha ho hs hi no h3
  refine ⟨α,fun R hR=>?_⟩
  let a:=R.coeff 3
  let T:=R-a • X^3
  have hT : T.natDegree≤2 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    change (R-a • X^3).coeff n=0
    rw [coeff_sub,Polynomial.smul_eq_C_mul,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow]
    by_cases e : n=3
    · subst n;simp [a]
    · have zz : R.coeff n=0 := coeff_eq_zero_of_natDegree_lt (by omega)
      simp [e,zz]
  have he := contrast_residual_grade (A:=A) (v:=v) P T (natDegree_mul_le.trans (by omega : T.natDegree+P.natDegree≤5))
    (cheap T hT)
  have hx : contrastResidual A v P T∈escape7 A := (show zeroSpace A 6≤escape7 A from le_sup_left) he
  have hy:contrastResidual A v P T+a • (contrastResidual A v P (X^3)-α • evalNodes A ghost7)=
      contrastResidual A v P R-(α*a) • evalNodes A ghost7 := by
    simp only [T,map_sub,map_smul,smul_sub,smul_smul]
    rw [mul_comm a α]
    abel
  rw [←hy]
  exact (escape7 A).add_mem hx ((escape7 A).smul_mem a eq)

omit [CharZero K] in
theorem joint_chain_core {c:Vec K (s+1)} {P:K[X]}
    (hc:U.map (diag c)≤U) (hv:U.map (diag v)≤U)
    (fit:v*w-weightedEval c w P∈U) {x τ:K} (hn:τ≠P.eval x)
    {n:ℕ} {z:Vec K (s+1)} (hz:z∈chain (diag c) U w n) :
    fiber v τ (fiber c x z)∈U := by
  classical
  obtain ⟨u,hu,B,_,e⟩:=exists_head_poly hz
  have hm := profile_vanish_on_block hc hv fit hn
  have f : fiber v τ (fiber c x z)=fiber v τ (fiber c x u)+B.eval x • fiber v τ (fiber c x w) := by
    ext j
    by_cases h:c j=x <;> by_cases h':v j=τ <;> simp [fiber,h,h',e j]
  rw [f]
  exact U.add_mem (fiber_mem hv _ (fiber_mem hc _ hu)) (U.smul_mem _ hm)

/-- General chronological p12 probe with one legal leakage scalar. A joint
block is allowed to carry part of the head, but a mismatch makes that part
belong to the invariant core, which is exactly what prefix matching needs. -/
theorem chronological_multiplier_contrast (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    (hs:Saturation A b) (hi:b (Fin.last s)≠0)
    (hh:HeadData A r U w) (hV:U.map (diag v)≤U)
    (P Q:K[X]) (hP:P≠0) (hQ:Q≠0) (dP:P.natDegree≤3) (dQ:Q.natDegree≤3)
    (hpay:weightedEval (nodes A) v Q∈zeroSpace A 6)
    (fit:v*w-weightedEval (nodes A) w P∈U) (α:K)
    (leak:∀ R:K[X],R.natDegree≤3→
      contrastResidual A v P R-(α*R.coeff 3) • evalNodes A ghost7∈escape7 A) :
    ∃ k:Fin (s+1), Q.eval (nodes A k)≠0 ∧
      (nodes A k=1 ∨ (mesh6:K[X]).eval (nodes A k)=0) ∧
      ∀ R:K[X],(R*Q).natDegree≤3→(Paired.primitive ((R*Q)*P)).eval (nodes A k)=
        (α*(R*Q).coeff 3)*(ghost7:K[X]).eval (nodes A k) := by
  classical
  let c := nodes A
  let z := evalNodes A (Q*P)-weightedEval c v Q
  have no : ∀ j:Fin (s+1),Fin.last s<j→b j=0 := fun j h=>False.elim ((not_lt_of_ge (Fin.le_last j)) h)
  have zd : (Q*P).natDegree≤6 := natDegree_mul_le.trans (by omega)
  change weightedEval c v Q∈zeroSpace A 6 at hpay
  have znot : z∉U := by
    intro h
    have Z := zeroSpace_mono A (by decide : 5≤6) (hh.low h)
    have hp := (zeroSpace A 6).add_mem Z hpay
    have hp' : evalNodes A (Q*P)∈zeroSpace A 6 := by simpa only [z,sub_add_cancel] using hp
    exact (mul_ne_zero hQ hP) (explicit_separated ha ho (by decide) (by omega) _ zd hp')
  obtain ⟨tag,tagEq,tagC⟩:=joint_labels hh.inv hV
  obtain ⟨k,p,hp,before,bad⟩:=first_unmatched_block tag z U tagC znot
  let t:=c k
  let τ:=v k
  let Z0:=Q.eval t*(P.eval t-τ)
  have zlocal (j:Fin (s+1)) (hj:tag j=tag k) : z j=Z0 := by
    obtain ⟨hc,hv⟩:= (tagEq j k).mp hj
    simp [z,c,evalNodes,weightedEval_apply] at hc hv ⊢
    rw [hc,hv];dsimp [Z0,t,τ,c];ring
  have zd0 : Z0≠0 := by
    intro e
    apply bad
    exact ⟨0,U.zero_mem,fun j _ hj=>by rw [zlocal j hj,e];rfl⟩
  have q0 : Q.eval t≠0 := (mul_ne_zero_iff.mp zd0).1
  have mismatch : τ≠P.eval t := fun e => (mul_ne_zero_iff.mp zd0).2 (sub_eq_zero.mpr e.symm)
  have restrict_Z {z':Vec K (s+1)} (h:z'∈escape7 A) :
      fiber v τ (fiber c t z')∈U := by
    rw [hh.f7tail] at h
    exact joint_chain_core hh.inv hV fit mismatch h
  have cannot (y:Vec K (s+1)) (hy:y∈escape7 A) (ξ:K)
      (vals:∀ j:Fin (s+1),j.val<k.val+1→tag j=tag k→y j=ξ) : ξ=0 := by
    by_contra nz
    apply bad
    refine ⟨(Z0/ξ) • fiber v τ (fiber c t y),U.smul_mem _ (restrict_Z hy),?_⟩
    intro j hj etag
    obtain ⟨hc,hv⟩:=(tagEq j k).mp etag
    have hc' : c j=t := hc
    have hv' : v j=τ := hv
    simp only [Pi.smul_apply,smul_eq_mul,fiber,hv',hc',ite_true]
    rw [vals j hj etag,div_mul_cancel₀ _ nz,zlocal j etag]
  refine ⟨k,q0,?_,?_⟩
  · by_cases hk:k=Fin.last s
    · exact Or.inl (hk ▸ active_last_normal ha hs hi no)
    right
    have D := mesh_at_end ha ho hs hi no
    have E : (Pi.single (Fin.last s) 1-evalNodes A mesh6:Vec K (s+1))∈escape7 A :=
      (show zeroSpace A 6≤escape7 A from le_sup_left) D
    apply neg_eq_zero.mp (cannot _ E (- (mesh6:K[X]).eval t) ?_)
    intro j hj e
    have hj' : j≠Fin.last s := by
      intro z
      have hk' := (Fin.le_last k)
      have hlk : k.val<s := by
        have hne : k.val≠s := fun eq=>hk (Fin.ext eq)
        have hlt := k.isLt
        omega
      subst j;change s<k.val+1 at hj;omega
    have hcl : c j=t := (tagEq j k).mp e |>.1
    change (Pi.single (Fin.last s) (1:K):Vec K (s+1)) j-(mesh6:K[X]).eval (c j)=_
    rw [Pi.single_eq_of_ne hj',zero_sub,hcl]
  · intro R dr
    let S:=R*Q
    let F:=S*P
    let l:=α*S.coeff 3
    let y:=contrastResidual A v P S+mat A (weightedEval c p R)-l • evalNodes A ghost7
    have wp : weightedEval c p R∈U := by
      have h := poly_preserves hh.inv R p hp
      have eq : weightedEval c p R=fun j=>R.eval (c j)*p j := by ext j;simp
      rwa [eq]
    have ap : mat A (weightedEval c p R)∈escape7 A :=
      (show zeroSpace A 6≤escape7 A from le_sup_left) (mat_zeroSpace_charZero A 5 (hh.low wp))
    have he : y∈escape7 A := by
      have h := (escape7 A).add_mem (leak S dr) ap
      simpa only [y,l,sub_add_eq_add_sub] using h
    have eq0 := cannot y he ((Paired.primitive F).eval t-l*(ghost7:K[X]).eval t) (by
      intro j hj ej
      have hc : c j=t := (tagEq j k).mp ej |>.1
      have eq : mat A (evalNodes A F-weightedEval c v S) j=mat A (weightedEval c p R) j := by
        apply strictlyCausal_mat ha
        intro m hm
        have hm' : m<k := by change m.val<j.val at hm;change m.val<k.val;omega
        have hpm := before m hm'
        change evalNodes A F m-weightedEval c v S m=weightedEval c p R m
        simp only [weightedEval_apply,evalNodes,F,S,eval_mul]
        simp only [z,Pi.sub_apply,evalNodes,weightedEval_apply,eval_mul] at hpm
        rw [hpm];ring
      dsimp only [y]
      rw [Pi.sub_apply,Pi.add_apply,contrastResidual_apply,Pi.sub_apply]
      change (Paired.primitive F).eval (c j)-mat A (evalNodes A F-weightedEval c v S) j+
        mat A (weightedEval c p R) j-l*(ghost7:K[X]).eval (c j)=_
      rw [eq,sub_add_cancel,hc])
    exact sub_eq_zero.mp eq0

end RKCert.Paired.OrderTwelve

