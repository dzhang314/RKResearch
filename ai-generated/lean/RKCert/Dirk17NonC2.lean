module
public import RKCert.Dirk17QuarticBudget
public import RKCert.RadauMissingRoot
public import RKCert.Dirk17RadauFourOmitted
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
@[expose] public section
namespace RKCert.Paired.Seventeen
open Module Polynomial RKCert.Endpoint RKCert.Paired.Terminal RKCert.RadauEight
variable {K:Type*} [Field K] [CharZero K] {A:Fin 23→Fin 23→K} {b θ:Vec K 23} {Q:K[X]}
noncomputable section
set_option maxRecDepth 4000
/-- Purely finite choice of as many omitted roots as the physical clean
site count permits. The only splitting assumption is on the fixed grid. -/
theorem omitted_radau_eight (S:Finset K) {n:ℕ} (room:n+S.card≤9)
    (sp:(grid K).Splits):
    ∃v:Fin n→K, Function.Injective v ∧ (∀k,(grid K).eval (v k)=0) ∧ ∀k,v k∉S:=by
  classical
  let D:K[X]:=grid K
  let Λ:=D.roots.toFinset
  let E:=Λ \ S
  have deg:D.natDegree=9:=grid_degree
  have dn:D≠0:=fun h=>by rw [h,natDegree_zero] at deg;omega
  have big:Λ.card=9:=by
    change D.roots.toFinset.card=_
    rw [Multiset.toFinset_card_of_nodup (nodup_roots grid_separable),←sp.natDegree_eq_card_roots,deg]
  have card:n≤E.card:=by
    have cc:=Finset.le_card_sdiff S Λ
    change Λ.card-S.card≤E.card at cc;omega
  let pick:Fin n→E:=fun k=>(Fintype.equivFin E).symm ⟨k.val,by rw [Fintype.card_coe];have:=k.isLt;omega⟩
  let v:Fin n→K:=fun k=>(pick k).val
  have hit(k:Fin n):v k∈E:=(pick k).property
  refine ⟨v,?_,fun k=>((mem_roots dn).mp (Multiset.mem_toFinset.mp (Finset.mem_sdiff.mp (hit k)).1)).eq_zero,
    fun k=>(Finset.mem_sdiff.mp (hit k)).2⟩
  intro a b eqn
  exact Fin.ext (congrArg (fun x:Fin (Fintype.card E)=>x.val) ((Fintype.equivFin E).symm.injective (show pick a=pick b from Subtype.ext eqn)))

/-- A missing fixed Radau clean site must be a genuine root of the original
grade-five trace numerator. The test uses only actual row pairings. -/
theorem fifth_omitted (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17) (h:Unanchored A b)
    (tr:ReverseTrace A b 17 5 θ Q) (dQ:Q.natDegree≤8)
    (support:∀i,θ i≠0→b i≠0 ∧ tau A b i=0) {z:K}
    (root:(grid K).eval z=0) (off:z∉cleanSites A b):Q.eval z=0:=by
  classical
  let D:K[X]:=grid K
  obtain ⟨L,rep⟩:=(dvd_iff_isRoot.mpr (show D.IsRoot z from root))
  have deg:D.natDegree=9:=grid_degree
  have nz:D≠0:=fun e=>by rw [e,natDegree_zero] at deg;omega
  have ln:L≠0:=fun e=>nz (by rw [rep,e,mul_zero])
  have ld:=congrArg Polynomial.natDegree rep
  rw [natDegree_mul (X_sub_C_ne_zero _) ln,natDegree_X_sub_C,deg] at ld
  have null:weightedEval (mirror A) θ L=0:=by
    ext i
    by_cases zero:θ i=0
    · simp [zero]
    obtain ⟨bi,ti⟩:=support i zero
    have yn:mirror A i≠z:=fun eqn=>off (eqn ▸ mem_cleanSites i bi ti)
    have val:D.eval (mirror A i)=0:=unanchored_grid ha ho h i bi ti
    rw [rep,eval_mul,eval_sub,eval_X,eval_C] at val
    have lz: L.eval (mirror A i)=0:=(mul_eq_zero.mp val).resolve_left (sub_ne_zero.mpr yn)
    simp [lz]
  have paid:=tr.pair_polynomial_radau ho L (by omega)
  have swapped : row θ (weightedEval (mirror A) (1:Vec K 23) L)=row (weightedEval (mirror A) θ L) 1:=by
    simp only [row_apply,weightedEval_apply,Pi.one_apply,mul_one]
    apply Finset.sum_congr rfl;intro i _;ring
  rw [swapped,null,unitIntegral_apply] at paid
  have van:integral (L*Q)=0:=by rw [integral_eq,←formalPrimitive_eq_treePrimitive,←paid];simp
  rw [cardinal_eval rep.symm Q dQ] at van
  exact (mul_eq_zero.mp van).resolve_right (cardinal_nonzero rep.symm (by omega) ln)

/-- The unanchored p17/s23 case is impossible in any fixed splitting
field; no sign assumption remains. -/
theorem no_nonC2_if_split (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17)
    (sp:(grid K).Splits):q₂ (mat A) (nodes A) 1=0:=by
  by_contra non
  let H:=unanchored ha ho non
  have cap:=unanchored_clean_five ha ho non H
  obtain ⟨a,inj,roots,miss⟩:=omitted_radau_eight (cleanSites A b) (n:=4) (by omega) sp
  apply seventeen_five_visible ha ho (unanchored_joint_inside ha ho H) (jointWithOrigin_invariant _)
  intro v hv
  obtain ⟨Q,dq,fit,off,θ,tr,active⟩:=H.D.port_contrast ha ho (by decide) (by decide) hv (H.clean _ (zeroSpace_mono A (by decide) hv))
  have qa(i:Fin 4):Q.eval (a i)=0:=fifth_omitted ha ho H tr (by omega) active (roots i) (miss i)
  have zero:Q=0:=by
    by_contra nz
    let y:=mirror A
    have ac(i:Fin 23)(v:diag y θ i≠0):b i≠0 ∧ tau A b i=0:=
      active i (fun zero=>v (by rw [diag_apply,zero,mul_zero]))
    obtain ⟨i,vi,bi,ti,_,tests⟩:=H.D.physical_reverse_pivot ha ho (H.D.nonlocal_cubic ha ho) (by decide) (by decide)
      (tr.clock (by decide)) ac (mul_ne_zero X_ne_zero nz)
    have yn:y i≠0:=fun zero=>vi (by change y i*θ i=0;rw [zero,zero_mul])
    have clean:=mem_cleanSites i bi ti
    have fresh(k:Fin 4):y i≠a k:=fun eqn=>miss k (eqn ▸ clean)
    have j₁: (primitive (X*Q)).eval (y i)=0:=by simpa only [pow_zero,one_mul,formalPrimitive_eq_treePrimitive] using tests 0 (by decide)
    have j₂: (primitive (X^2*Q)).eval (y i)=0:=by simpa only [pow_one,pow_two,mul_assoc,formalPrimitive_eq_treePrimitive] using tests 1 (by decide)
    exact nz (radau8_four_omitted a (y i) Q inj roots (unanchored_grid ha ho H i bi ti) fresh yn dq qa j₁ j₂)
  have hit(i:Fin 23) (ti:tau A b i≠0):v i=0:=by simpa [zero] using fit i ti
  apply jointWithOrigin_iff.mpr
  refine ⟨⟨?_,?_⟩,by omega⟩ <;> ext i
  · by_cases t:tau A b i=0
    · exact off i t
    · simp [hit i t]
  · by_cases t:tau A b i=0
    · simp [t]
    · simp [hit i t]

/-- Every characteristic-zero all-tree order-17 DIRK on 23 original rows
must satisfy C(2); unrestricted clocks, weights and diagonal entries. -/
theorem no_nonC2 (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17):q₂ (mat A) (nodes A) 1=0:=by
  let φ:K→+*AlgebraicClosure K:=algebraMap K (AlgebraicClosure K)
  have vanished:=no_nonC2_if_split (lowerTriangular_map ha φ) (ho.map φ) (IsAlgClosed.splits _)
  ext i
  apply φ.injective
  have q:=congrFun vanished i
  simpa only [q₂,Pi.sub_apply,Pi.smul_apply,Pi.one_apply,smul_eq_mul,mat_apply,diag_apply,nodes,
    map_sub,map_mul,map_sum,map_one,map_ofNat,Pi.zero_apply,map_zero] using q
end
end RKCert.Paired.Seventeen
