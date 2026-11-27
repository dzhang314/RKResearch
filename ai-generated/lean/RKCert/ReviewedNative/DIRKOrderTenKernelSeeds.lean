module

public import RKCert.ReviewedNative.DIRKOrderTenSaturation

@[expose] public section

/-! # Actual forward and reverse cubic Volterra kernel seeds at DIRK10 equality -/
namespace RKResearch.Certified.Graded.CrossedOrderTen

open Module RKResearch FiniteRootedTree Reverse
open scoped Matrix FiniteRootedTree BigOperators
noncomputable section
variable {K : Type*} [Field K]
variable {A : Matrix (Fin 11) (Fin 11) K} {b : Fin 11 → K}

private theorem two_constraints_have_kernel
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (E F : Submodule K V) (T : V →ₗ[K] V) (L : V →ₗ[K] K)
    (im : E ≤ F.comap T) (dim : finrank K F+2≤finrank K E) :
    ∃ v∈E, v≠0 ∧ T v=0 ∧ L v=0 := by
  let f : E →ₗ[K] F := (T.comp E.subtype).codRestrict F (fun v => im v.property)
  let h := f.prod (L.comp E.subtype)
  have ni : ¬ Function.Injective h := by
    intro yes
    have counts := LinearMap.finrank_le_finrank_of_injective yes
    rw [Module.finrank_prod,Module.finrank_self] at counts
    omega
  by_contra! bad
  apply ni
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  have zf : T (z : V)=0 := congrArg (fun y : F × K => (y.1 : V)) hz
  have zl : L (z : V)=0 := congrArg Prod.snd hz
  apply Subtype.ext
  by_contra h
  exact bad (z : V) z.property h zf zl

private theorem first_nonzero (v : Fin 11 → K) (nz : v ≠ 0) :
    ∃ i, v i≠0 ∧ ∀ j < i, v j=0 := by
  classical
  let S := Finset.univ.filter (fun i => v i≠0)
  have hex : S.Nonempty := by
    by_contra hn
    apply nz
    ext i
    change v i=0
    by_contra hi
    apply hn
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩
  let i := S.min' hex
  refine ⟨i,(Finset.mem_filter.mp (Finset.min'_mem S hex)).2,?_⟩
  intro j hj
  by_contra! live
  exact (not_lt_of_ge (S.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ j,live⟩))) hj

private theorem latest_nonzero (v : Fin 11 → K) (nz : v ≠ 0) :
    ∃ i, v i≠0 ∧ ∀ j, i < j → v j=0 := by
  classical
  let S := Finset.univ.filter (fun i => v i≠0)
  have hex : S.Nonempty := by
    by_contra hn
    apply nz
    ext i
    change v i=0
    by_contra hi
    apply hn
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩
  let i := S.max' hex
  refine ⟨i,(Finset.mem_filter.mp (Finset.max'_mem S hex)).2,?_⟩
  intro j hj
  by_contra! live
  exact (not_lt_of_ge (S.le_max' j (Finset.mem_filter.mpr ⟨Finset.mem_univ j,live⟩))) hj

private theorem clock_nonzero (ho : HasOrder 10 A b) : nodes A ≠ 0 := by
  intro h
  have e := ho.hasQuadratureOrder 1 (by decide)
  change (2:K)*(b ⬝ᵥ (nodes A)^1)=1 at e
  simp [h] at e

private theorem front_cubic_not_kernel (ha : A.IsLowerTriangular)
    (ho : HasOrder 10 A b) (S : Saturated A b) :
    volterra A (monomialStageDefect A 2)≠0 := by
  obtain ⟨i,ni,pre⟩ := first_nonzero (nodes A) (clock_nonzero ho)
  have pivot (k : Nat) (nk : k≠0) (j : Fin 11) (h : j ≤ i) :
      mat A ((nodes A)^k) j = A j j * (nodes A j)^k := by
    have z : ∀ l : Fin 11, l < j → ((nodes A)^k) l=0 := by
      intro l hl
      rw [Pi.pow_apply,pre l (hl.trans_le h),zero_pow nk]
    rw [mat_apply,lowerTriangular_mulVec_pivot ha j _ z,Pi.pow_apply]
  have q : (2:K)*(A i i*nodes A i) - (nodes A i)^2=0 := by
    have e := congrFun S.c2 i
    change (2:K)*mat A ((nodes A)^1) i - (nodes A i)^2=0 at e
    rw [pivot 1 (by decide) i le_rfl,pow_one] at e
    exact e
  have di : (2:K)*A i i = nodes A i := by
    have eq : ((2:K)*A i i - nodes A i) * nodes A i=0 := by linear_combination q
    exact sub_eq_zero.mp ((mul_eq_zero.mp eq).resolve_right ni)
  have dn : A i i ≠ 0 := by
    intro zz
    apply ni
    linear_combination -di + (2:K)*zz
  have val : monomialStageDefect A 2 i ≠ 0 := by
    intro hz
    change (3:K)*mat A ((nodes A)^2) i - (nodes A i)^3=0 at hz
    rw [pivot 2 (by decide) i le_rfl] at hz
    apply pow_ne_zero 3 ni
    linear_combination 2*hz - 3*(nodes A i)^2*di
  have clean : ∀ j < i, monomialStageDefect A 2 j=0 := by
    intro j hj
    change (3:K)*mat A ((nodes A)^2) j - (nodes A j)^3=0
    rw [pivot 2 (by decide) j hj.le, pre j hj]
    simp
  intro h
  have k := congrFun h i
  rw [volterra_pivot ha i _ clean] at k
  exact val ((mul_eq_zero.mp k).resolve_left (neg_ne_zero.mpr (pow_ne_zero 2 dn)))

/-- A true stage column of grade at most three, in the Volterra kernel,
with zero starting value and a nonzero origin-factored scalar profile. -/
structure FrontSeed (A : Matrix (Fin 11) (Fin 11) K) where
  v : Fin 11 → K
  a : Fin 4 → K
  d : K
  form : v=coeffEval A 3 a+d • monomialStageDefect A 2
  a0 : a 0=0
  a_live : a≠0
  pivot : Fin 11
  live : v pivot≠0
  before : ∀ j < pivot, v j=0
  explicit : A pivot pivot=0
  interior : 0 < pivot

theorem exists_front_seed (ha : A.IsLowerTriangular)
    (ho : HasOrder 10 A b) (S : Saturated A b) : Nonempty (FrontSeed A) := by
  obtain ⟨v,hv,nv,kv,v0⟩ := two_constraints_have_kernel (treeSpace A 3) (zeroSpace A 5)
    (volterra A) (LinearMap.proj 0) (volterra_treeSpace ho 3 (by decide))
    (by rw [S.f5,S.e3])
  have sp := treeSpace_coeff_sup ho (q:=3) (by decide)
  rw [sp] at hv
  obtain ⟨_,⟨a,rfl⟩,u,hu,rfl⟩ := Submodule.mem_sup.mp hv
  rw [zeroSpace_three_of_C2 A S.c2] at hu
  obtain ⟨d,rfl⟩ := Submodule.mem_span_singleton.mp hu
  have g0 : monomialStageDefect A 2 0=0 :=
    zeroSpace_at_zero_row S.physical_origin 3 (monomialStageDefect_mem A 2)
  have a0 : a 0=0 := by
    change (coeffEval A 3 a + d • monomialStageDefect A 2) 0=0 at v0
    simpa only [Pi.add_apply,Pi.smul_apply,g0,smul_zero,add_zero,
      coeffEval_at_zero_row S.physical_origin] using v0
  have an : a ≠ 0 := by
    intro z
    subst a
    rw [map_zero,zero_add,map_smul] at kv
    have d0 := (smul_eq_zero.mp kv).resolve_right (front_cubic_not_kernel ha ho S)
    exact nv (by simp [d0])
  obtain ⟨i,vi,pre⟩ := first_nonzero _ nv
  have di := congrFun kv i
  rw [volterra_pivot ha i _ pre] at di
  have ad : A i i=0 := by
    exact sq_eq_zero_iff.mp (neg_eq_zero.mp ((mul_eq_zero.mp di).resolve_right vi))
  have pos : 0 < i := by
    by_contra! z
    have z' : i=0 := le_antisymm z (Fin.zero_le i)
    subst i
    exact vi v0
  exact ⟨⟨_,a,d,rfl,a0,an,i,vi,pre,ad,pos⟩⟩


/-- The physical row version of Volterra, with the original clock
replaced by its complement and the original matrix transposed. -/
def backVolterra (A : Matrix (Fin 11) (Fin 11) K) :
    (Fin 11 → K) →ₗ[K] (Fin 11 → K) :=
  (diag (reflectedClock A)).comp (mat A.transpose)
    - (mat A.transpose).comp (diag (reflectedClock A))
    - (mat A.transpose).comp (mat A.transpose)

theorem backVolterra_adjoint (w v : Fin 11 → K) :
    row (backVolterra A w) v=row w (volterra A v) := by
  have hy (x : Fin 11 → K) : diag (reflectedClock A) x = x-diag (nodes A) x := by
    ext i
    simp only [diag_apply,Pi.sub_apply,Pi.one_apply]
    ring
  simp only [backVolterra,volterra,LinearMap.sub_apply,LinearMap.comp_apply,map_sub,
    row_diag,row_mat_transpose,hy]
  ring

private theorem backVolterra_pivot (ha : A.IsLowerTriangular) (i : Fin 11)
    (v : Fin 11 → K) (after : ∀ j, i < j → v j=0) :
    backVolterra A v i=-(A i i)^2*v i := by
  have hz (j : Fin 11) (hij : i < j) : mat A.transpose v j = 0 := by
    rw [transpose_mat_pivot ha j v (fun l hl => after l (hij.trans hl)), after j hij,mul_zero]
  have hp (j : Fin 11) (hij : i < j) : diag (reflectedClock A) v j = 0 := by
    rw [diag_apply,after j hij,mul_zero]
  simp only [backVolterra,LinearMap.sub_apply,LinearMap.comp_apply,Pi.sub_apply]
  rw [diag_apply,transpose_mat_pivot ha i v after,
    transpose_mat_pivot ha i _ hp,transpose_mat_pivot ha i _ hz,
    transpose_mat_pivot ha i v after,diag_apply]
  ring

private theorem back_cubic_earns_pivot (ha : A.IsLowerTriangular)
    (ho : HasOrder 10 A b) (S : Saturated A b) :
    ∃ i, reflectedStageRow A b 2 i ≠ 0 ∧ A i i≠0 ∧
      ∀ j, i < j → reflectedStageRow A b 2 j=0 := by
  have act : diag (reflectedClock A) b≠0 := by
    intro z
    exact reflected_target_ne_zero ho (by decide) (by rw [z,row_apply,zero_dotProduct])
  obtain ⟨i,live,after⟩ := latest_nonzero _ act
  change reflectedClock A i * b i ≠ 0 at live
  have nb : b i≠0 := (mul_ne_zero_iff.mp live).2
  have ny : reflectedClock A i≠0 := (mul_ne_zero_iff.mp live).1
  have wzero (k : Nat) (nk : k≠0) (j : Fin 11) (hj : i < j) :
      reflectedStageWeight A b k j=0 := by
    have h := after j hj
    rw [diag_apply] at h
    rcases mul_eq_zero.mp h with h | h
    · simp [reflectedStageWeight,h,zero_pow nk]
    · simp [reflectedStageWeight,h]
  have comp (k : Nat) (nk : k≠0) (j : Fin 11) (hj : i ≤ j) :
      reflectedStageRow A b k j =
        ((k+1:Nat):K)*(A j j * (b j * (reflectedClock A j)^k)) -
          b j*(reflectedClock A j)^(k+1) := by
    change ((k+1:Nat):K)*mat A.transpose (reflectedStageWeight A b k) j -
      b j*(reflectedClock A j)^(k+1)=_
    rw [transpose_mat_pivot ha j _ (fun l hl => wzero k nk l (hj.trans_lt hl))]
  have d2 := comp 1 (by decide) i le_rfl
  rw [S.d2] at d2
  simp only [Pi.zero_apply,Nat.reduceAdd,Nat.cast_ofNat,pow_one] at d2
  have d : (2:K)*A i i = reflectedClock A i := by
    have q : ((2:K)*A i i - reflectedClock A i) * (b i*reflectedClock A i)=0 := by
      linear_combination -d2
    exact sub_eq_zero.mp ((mul_eq_zero.mp q).resolve_right (mul_ne_zero nb ny))
  have nz : A i i≠0 := by
    intro z
    apply ny
    linear_combination -d + (2:K)*z
  have ng : reflectedStageRow A b 2 i≠0 := by
    intro z
    rw [comp 2 (by decide) i le_rfl] at z
    simp only [Nat.reduceAdd,Nat.cast_ofNat] at z
    apply mul_ne_zero nb (pow_ne_zero 3 ny)
    linear_combination 2*z-3*(b i*(reflectedClock A i)^2)*d
  refine ⟨i,ng,nz,?_⟩
  intro j hj
  have w2 := wzero 2 (by decide) j hj
  have w3 := wzero 3 (by decide) j hj
  change b j*(reflectedClock A j)^2=0 at w2
  change b j*(reflectedClock A j)^3=0 at w3
  rw [comp 2 (by decide) j hj.le]
  change (3:K)*(A j j*(b j*(reflectedClock A j)^2))-b j*(reflectedClock A j)^3=0
  rw [w2,w3]
  simp

private theorem back_cubic_not_kernel (ha : A.IsLowerTriangular)
    (ho : HasOrder 10 A b) (S : Saturated A b) :
    backVolterra A (reflectedStageRow A b 2)≠0 := by
  obtain ⟨i,live,nz,after⟩ := back_cubic_earns_pivot ha ho S
  intro q
  have hp := congrFun q i
  rw [backVolterra_pivot ha i _ after] at hp
  exact (neg_ne_zero.mpr (pow_ne_zero 2 nz))
    ((mul_eq_zero.mp hp).resolve_right live)


private def backSpanMap (A : Matrix (Fin 11) (Fin 11) K) (b : Fin 11 → K) :
    ((Fin 4 → K) × K) →ₗ[K] (Fin 11 → K) :=
  ((diag b).comp (coeffEval A 3)).coprod
    ((LinearMap.id : K →ₗ[K] K).smulRight (reflectedStageRow A b 2))

private theorem backSpanMap_eq (a : Fin 4 → K) (d : K) :
    backSpanMap A b (a,d) = diag b (coeffEval A 3 a) + d • reflectedStageRow A b 2 := rfl

private theorem row_diag_bpow (v : Fin 11 → K) (i : Nat) :
    row (diag b v) ((nodes A)^i) = probe A b i v := by
  simp only [probe,row_apply,dotProduct,diag_apply,Pi.pow_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem clock_mem (i : Fin 4) : (nodes A)^i.val ∈ treeSpace A 3 := by
  change (fun j => (nodes A j)^i.val) ∈ treeSpace A 3
  rw [← normTree_clockTree,← coeffEval_single A 3 i]
  exact coeffEval_mem_treeSpace A 3 (Pi.single i 1)

private theorem backSpanMap_inj (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b)
    (S : Saturated A b) : Function.Injective (backSpanMap A b) := by
  apply (injective_iff_map_eq_zero _).mpr
  rintro ⟨a,d⟩ h
  rw [backSpanMap_eq] at h
  have tests (i : Fin 4) : probe A b i.val (coeffEval A 3 a)=0 := by
    have hq := congrArg (fun w => row w ((nodes A)^i.val)) h
    simp only [row_apply,add_dotProduct,smul_dotProduct,zero_dotProduct,smul_eq_mul] at hq
    change row (diag b (coeffEval A 3 a)) ((nodes A)^i.val) +
      d * row (reflectedStageRow A b 2) ((nodes A)^i.val)=0 at hq
    have hp := reflectedStageRow_treeSpace ho 3 2 (by decide) (clock_mem (A:=A) i)
    change row (reflectedStageRow A b 2) ((nodes A)^i.val)=0 at hp
    rwa [row_diag_bpow,hp,mul_zero,add_zero] at hq
  have za : a=0 := by
    ext i
    apply moments_detect ho (d:=1) (by decide) (by omega) (fun k l=>by
      have := k.isLt
      have := l.isLt
      omega) a _ i
    intro k
    have hk := tests k
    rwa [probe_coeffEval ho (by have := k.isLt; omega)] at hk
  rw [za,map_zero,map_zero,zero_add] at h
  have zd : d=0 := by
    by_contra nz
    have gg : reflectedStageRow A b 2=0 := (smul_eq_zero.mp h).resolve_left nz
    apply back_cubic_not_kernel ha ho S
    rw [gg,map_zero]
  exact Prod.ext za zd

private theorem volterra_terminal_zero (S : Saturated A b) :
    volterra A (coordinate (Fin.last 10))=0 := by
  let t : Fin 11 := Fin.last 10
  let e : Fin 11 → K := coordinate t
  have m0 : mat A e=0 := by
    classical
    ext i
    simp only [e,coordinate,mat_apply,Matrix.mulVec,dotProduct_single_one,Pi.zero_apply]
    exact S.last_column i
  have d0 : diag (nodes A) e=e := by
    classical
    ext i
    by_cases hi : i=t
    · subst i
      simp only [diag_apply,e,t,coordinate,Pi.single_eq_same,S.last_node,mul_one]
    · simp [diag_apply,e,coordinate,hi]
  change volterra A e=0
  simp only [volterra,LinearMap.sub_apply,LinearMap.comp_apply,m0,d0,map_zero,sub_zero]

private theorem backCubic_terminal_zero (S : Saturated A b) :
    reflectedStageRow A b 2 (Fin.last 10) = 0 := by
  have Q (k : Nat) : mat A.transpose (reflectedStageWeight A b k) (Fin.last 10) = 0 := by
    simp only [mat_apply,Matrix.mulVec_apply_eq_sum,Matrix.transpose_apply,S.last_column,
      zero_mul,Finset.sum_const_zero]
  have yt : reflectedClock A (Fin.last 10)=0 := by
    change 1-nodes A (Fin.last 10)=0
    rw [S.last_node,sub_self]
  change (3:K)*mat A.transpose (reflectedStageWeight A b 2) (Fin.last 10) -
    b (Fin.last 10)*(reflectedClock A (Fin.last 10))^3=0
  rw [Q,yt]; simp

private theorem backSpan_to_annih (ho : HasOrder 10 A b) (S : Saturated A b) :
    (backSpanMap A b).range ≤ (zeroAt (annih (treeSpace A 4)) (Fin.last 10)).comap
      (backVolterra A) := by
  intro w hw
  obtain ⟨⟨a,d⟩,rfl⟩ := hw
  apply mem_zeroAt.mpr
  constructor
  · apply mem_annih.mpr
    intro v hv
    rw [backVolterra_adjoint,backSpanMap_eq]
    have h := volterra_treeSpace ho 4 (by decide) hv
    have hz := zeroSpace_le_treeSpace _ _ h
    have g := reflectedStageRow_treeSpace ho 6 2 (by decide) hz
    change row (reflectedStageRow A b 2) (volterra A v)=0 at g
    rw [coeffEval_apply,map_sum]
    simp only [row_apply,add_dotProduct,smul_dotProduct,smul_eq_mul]
    rw [show (reflectedStageRow A b 2) ⬝ᵥ (volterra A v)=0 from g,mul_zero,add_zero]
    simp only [sum_dotProduct]
    apply Finset.sum_eq_zero
    intro j _
    rw [map_smul,smul_dotProduct]
    have hj : (diag b (normTree A (clockTree j.val))) ⬝ᵥ (volterra A v)=0 := by
      change row (diag b (normTree A (clockTree j.val))) (volterra A v) = 0
      rw [normTree_clockTree]
      have eq := probe_zeroSpace ho (b:=b) (k:=j.val) (by have := j.isLt; omega) h
      change probe A b j.val (volterra A v)=0 at eq
      simpa only [probe,row_apply,dotProduct,diag_apply] using eq
    rw [hj,smul_zero]
  · rw [←row_coordinate (backVolterra A (backSpanMap A b (a,d))) (Fin.last 10),
      backVolterra_adjoint,volterra_terminal_zero S,map_zero]

/-- The backward kernel is a genuine weighted row, not a reflected RK
method constructed by inverting output weights. -/
structure BackSeed (A : Matrix (Fin 11) (Fin 11) K) (b : Fin 11 → K) where
  v : Fin 11 → K
  a : Fin 4 → K
  d : K
  form : v=diag b (coeffEval A 3 a)+d • reflectedStageRow A b 2
  a_last : coeffEval A 3 a (Fin.last 10)=0
  a_live : a≠0
  pivot : Fin 11
  live : v pivot≠0
  after : ∀ j, pivot < j → v j=0
  explicit : A pivot pivot=0
  interior : pivot < Fin.last 10

theorem exists_back_seed (ha : A.IsLowerTriangular)
    (ho : HasOrder 10 A b) (S : Saturated A b) : Nonempty (BackSeed A b) := by
  let T := (backSpanMap A b).range
  let Z := zeroAt (annih (treeSpace A 4)) (Fin.last 10)
  have rt : finrank K T=5 := by
    have q := (LinearEquiv.ofInjective _ (backSpanMap_inj ha ho S)).finrank_eq
    simpa only [T,Module.finrank_prod,Module.finrank_fin_fun,Module.finrank_self,Nat.reduceAdd] using q.symm
  have rz : finrank K Z=3 := by
    have h := finrank_zeroAt_annih (treeSpace A 4) (Fin.last 10)
      (endpoint_coordinate_out_of_zero_row ho (by decide) S.physical_origin S.last_live S.last_node)
    have k := finrank_annih (treeSpace A 4)
    rw [S.e4,Fintype.card_fin] at k
    dsimp only [Z]
    omega
  obtain ⟨v,hv,nv,kv,vt⟩ := two_constraints_have_kernel T Z (backVolterra A)
    (LinearMap.proj (Fin.last 10)) (backSpan_to_annih ho S) (by rw [rt,rz])
  obtain ⟨⟨a,d⟩,rfl⟩ := hv
  have aval : coeffEval A 3 a (Fin.last 10)=0 := by
    rw [backSpanMap_eq] at vt
    change (diag b (coeffEval A 3 a)+d • reflectedStageRow A b 2) (Fin.last 10)=0 at vt
    rw [Pi.add_apply,Pi.smul_apply,diag_apply,backCubic_terminal_zero S,smul_zero,add_zero] at vt
    exact (mul_eq_zero.mp vt).resolve_left S.last_live
  have an : a≠0 := by
    intro za
    subst a
    rw [backSpanMap_eq,map_zero,map_zero,zero_add,map_smul] at kv
    have zd := (smul_eq_zero.mp kv).resolve_right (back_cubic_not_kernel ha ho S)
    exact nv (by simp [backSpanMap_eq,zd])
  obtain ⟨i,va,aft⟩ := latest_nonzero _ nv
  have nk := congrFun kv i
  rw [backVolterra_pivot ha i _ aft] at nk
  have di : A i i=0 := sq_eq_zero_iff.mp (neg_eq_zero.mp ((mul_eq_zero.mp nk).resolve_right va))
  have il : i < Fin.last 10 := lt_of_le_of_ne (Fin.le_last i) (fun h => va (h.symm ▸ vt))
  exact ⟨⟨_,a,d,backSpanMap_eq a d,aval,an,i,va,aft,di,il⟩⟩

end
end RKResearch.Certified.Graded.CrossedOrderTen
