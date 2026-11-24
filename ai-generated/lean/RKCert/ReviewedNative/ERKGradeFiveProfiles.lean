module

public import RKCert.ReviewedNative.ForwardNodalGain
public import RKCert.ReviewedNative.OneOffWideProfiles
public import RKCert.ReviewedNative.OneOffCleanClocks
public import RKCert.ReviewedNative.ClockHeadFibers

@[expose] public section

/-! # The native minimal grade-five profiles under genuine separation
No output row is assumed. The quadratic defect is the existing OneOff.g,
not a redefinition. The two exact unit steps follow from native Hermite
gain at grades three and four. -/
namespace RKResearch.Certified.Graded
open RKResearch Polynomial Module OneOff RKCert.OneEscape
open scoped Classical Matrix

variable {K : Type*} [Field K] {s q : ℕ} {A : Matrix (Fin s) (Fin s) K}

theorem PolySeparated.coeff (sep : PolySeparated A q) :
    ∀ a, coeffEval A q a ∈ zeroSpace A q → a=0 := by
  intro a ha
  have e := sep (ofFn (q+1) a) (by
    exact Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) a))
    (by rw [OneOff.evalNodes_ofFn]; exact ha)
  ext i
  have h := congrArg (fun P : K[X] => P.coeff i.val) e
  simpa only [ofFn_coeff_eq_val_of_lt _ i.isLt,coeff_zero,Pi.zero_apply] using h

variable [CharZero K]

/-- Four strict native gains leave no room for any larger grade in a
hypothetical four-dimensional grade-five space. -/
theorem minimal_grade_five_ranks (ha : ∀ i j,i ≤ j → A i j=0)
    (sep : PolySeparated A 5) (cap : finrank K (zeroSpace A 5)≤4) :
    finrank K (zeroSpace A 2)=1 ∧ finrank K (zeroSpace A 3)=2 ∧
      finrank K (zeroSpace A 4)=3 ∧ finrank K (zeroSpace A 5)=4 := by
  have step (j : ℕ) (lo : 1≤j) (hi : j+1≤5) :
      finrank K (zeroSpace A j)<finrank K (zeroSpace A (j+1)) :=
    Submodule.finrank_lt_finrank_of_lt (zeroSpace_strict_of_separation ha sep.coeff lo hi)
  have s1 := step 1 (by decide) (by decide)
  have s2 := step 2 (by decide) (by decide)
  have s3 := step 3 (by decide) (by decide)
  have s4 := step 4 (by decide) (by decide)
  simp only [Nat.reduceAdd] at s1 s2 s3 s4
  omega

theorem minimum_five_clock_step (ha : ∀ i j,i ≤ j → A i j=0)
    (sep : PolySeparated A 5) (cap : finrank K (zeroSpace A 5)≤4)
    {j : ℕ} (lo : 3≤j) (hi : j≤4) :
    zeroSpace A (j+1)=zeroSpace A j ⊔ (zeroSpace A j).map (diag (nodes A)) := by
  obtain ⟨_,r3,r4,r5⟩ := minimal_grade_five_ranks ha sep cap
  have unit : finrank K (zeroSpace A (j+1))=finrank K (zeroSpace A j)+1 := by
    obtain rfl|rfl : j=3 ∨ j=4 := by omega
    · change finrank K (zeroSpace A 4)=_
      omega
    · change finrank K (zeroSpace A 5)=_
      omega
  apply zeroSpace_clock_step_of_unit unit.le
  intro inv
  have h := clock_invariant_outgoing ha (sep.mono (by omega : j≤5)) le_rfl inv
  omega

/-- An off-clock quadratic eigenvector earns its actual chronological
origin and support, without compressing or relabelling early rows. -/
theorem origin_of_dependent_quadratic (ha : ∀ i j,i ≤ j → A i j=0)
    (sep : PolySeparated A 5)
    (dep : diag (nodes A) (g A)∈Submodule.span K {g A}) :
    ∃ a : K, ∃ i : Fin s, Origin A a i := by
  classical
  let S : Set (Fin s) := {i | nodes A i≠0}
  have ex : S.Nonempty := by
    by_contra z
    have ce : nodes A=0 := funext fun i => by
      by_contra h
      exact z ⟨i,h⟩
    exact sep.nodes_not_mem (by decide) (ce ▸ (zeroSpace A 5).zero_mem)
  obtain ⟨i,ni,first⟩ := wellFounded_lt.has_min S ex
  let a := nodes A i
  change a≠0 at ni
  have pre (j : Fin s) (hj : j < i) : nodes A j=0 := by
    by_contra z
    exact first j z hj
  have gi : g A i= -a^2/2 := by
    rw [g_apply, causal_mat ha i _ pre]
    ring
  have gn : g A i≠0 := by rw [gi]; exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ ni)) (by norm_num)
  obtain ⟨μ,he⟩ := Submodule.mem_span_singleton.mp dep
  have e (j : Fin s) := congrFun he j
  have mu : μ=a := by
    apply mul_right_cancel₀ gn
    exact e i
  refine ⟨a,i,⟨ni,rfl,pre,gi,?_,?_⟩⟩
  · intro j hj
    rw [g_apply,causal_mat ha j _ (fun k hk =>pre k (hk.trans hj)),pre j hj]
    simp
  · intro j hj
    exact (mul_right_cancel₀ hj (e j)).symm.trans mu

/-- The already checked square analyses yield constant amplitude under
separation and the rank-three/rank-four budget alone, independent of p9. -/
theorem constant_amplitude_of_grade_five_dependence (ha : ∀ i j,i ≤ j → A i j=0)
    (sep : PolySeparated A 5) (cap : finrank K (zeroSpace A 5)≤4)
    (dep : diag (nodes A) (g A)∈Submodule.span K {g A}) :
    ∃ (a d : K) (i j : Fin s), ConstantAmplitude A a d i j := by
  obtain ⟨_,r3,r4,_⟩ := minimal_grade_five_ranks ha sep cap
  obtain ⟨a,i,O⟩ := origin_of_dependent_quadratic ha sep dep
  have s3 := (sep.mono (by decide : 3≤5)).coeff
  have s4 := sep.mono (by decide : 4≤5)
  obtain ⟨lam,qform⟩ := quadratic_defect_form ha s3 r3 O
  obtain ⟨j,F⟩ := first_h_split ha s3 O qform
  have span3 := rank_two_span ha s3 r3 O
  have amp : (g A)^2=baseAmp a • g A := by
    by_cases sq : (g A)^2∈zeroSpace A 3
    · exact constant_amplitude_of_dependent_square ha s4 r3 r4 O span3 qform F sq
    · have ind := independent_square_shape ha r3 r4 O F span3 sq
      by_cases on : g A j=0
      · exact False.elim (independent_square_on_first_impossible ha s4 O F qform ind on)
      · exact False.elim (independent_square_off_first_impossible ha s4 O F qform ind on)
  rcases F.alternative with ⟨on,nd,hj,e⟩|⟨off,ne,_,_,_⟩
  · change lam=twoLam a (nodes A j) at e
    subst lam
    exact ⟨a,nodes A j,i,j,O,rfl,on,nd,hj,F,amp,span3,qform⟩
  · exact False.elim (ne (amplitude_value amp off))

/-- If the minimal branch has one off clock, the actual fifth defect
space is its paid invariant off line and a quadratic clock head on Ag. -/
theorem OneOff.GlobalNormal.five_defect_of_minrank {a d : K} {i j : Fin s}
    (D : GlobalNormal A a d i j) (ha : ∀ i j,i ≤ j → A i j=0)
    (sep : PolySeparated A 5) (cap : finrank K (zeroSpace A 5)≤4)
    {v : Fin s→K} (vm : v∈zeroSpace A 5) :
    ∃ (α : K) (P : K[X]), P.natDegree≤2 ∧
      ∀ i, v i=α*g A i+P.eval (nodes A i)*h A i := by
  let U := Submodule.span K {g A}
  let C := diag (nodes A)
  have stable : U.map C≤U := by
    rintro _ ⟨_,u,rfl⟩
    obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp u
    rw [map_smul,D.base.origin.g_clock]
    exact U.smul_mem _ (U.smul_mem _ (Submodule.mem_span_singleton_self _))
  have e4 : zeroSpace A 4=chain C U (h A) 2 := by
    rw [D.span_four,D.base.span_three,Submodule.span_insert]
    change _ = (U ⊔ Submodule.span K {(C^0) (h A)}) ⊔ Submodule.span K {(C^1) (h A)}
    simp [U,C]
  have e5 := minimum_five_clock_step ha sep cap (j:=4) (by decide) (by decide)
  change zeroSpace A 5=_ at e5
  rw [e4,clock_chain_next stable (by decide)] at e5
  obtain ⟨u,hu,P,hP,eq⟩ := HeadFiber.exists_poly (e5 ▸ vm)
  obtain ⟨α,rfl⟩ := Submodule.mem_span_singleton.mp hu
  have pd : P.natDegree≤2 := by
    by_cases z : P=0
    · simp [z]
    · exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt z).mpr hP)
  exact ⟨α,P,pd,fun i=>by simpa [RKCert.Endpoint.weightedEval_apply] using congrFun eq i⟩

end RKResearch.Certified.Graded
