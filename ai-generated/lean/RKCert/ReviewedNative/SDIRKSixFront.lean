module

public import RKCert.ReviewedNative.SDIRKSixFlags
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp

@[expose] public section
namespace RKResearch.Certified.Graded.SDIRKSix
open RKResearch FiniteRootedTree
open scoped FiniteRootedTree Matrix
variable {K : Type*} [Field K] {s p : ℕ}

/-- The actual scalar-moment annihilator inside an ordinary physical flag. -/
def silent (A : Matrix (Fin s) (Fin s) K) (b : (Fin s → K)) (a q : ℕ) : Submodule K ((Fin s → K)) :=
  treeSpace A a ⊓ ⨅ i : Fin (q+1), LinearMap.ker (probe A b i.val)

theorem silent_mem {A : Matrix (Fin s) (Fin s) K} {b : (Fin s → K)} {a q : ℕ} {x : (Fin s → K)} :
    x ∈ silent A b a q ↔ x∈treeSpace A a ∧ ∀ i : Fin (q+1),probe A b i.val x=0 := by
  simp only [silent, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]

theorem zero_le_silent {A : Matrix (Fin s) (Fin s) K} {b : (Fin s → K)} {a q : ℕ}
    (ho : HasOrder p A b) (hp : a+q+1≤p) :
    zeroSpace A a ≤ silent A b a q := by
  intro x hx
  exact silent_mem.mpr ⟨zeroSpace_le_treeSpace A a hx,
    fun i => probe_zeroSpace ho (by omega) hx⟩

theorem silent_rank {A : Matrix (Fin s) (Fin s) K} {b : (Fin s → K)} {a q : ℕ}
    (ho : HasOrder p A b) (hq : q≤a) (hp : a+q+1≤p) :
    q+1+Module.finrank K (silent A b a q) ≤ Module.finrank K (treeSpace A a) := by
  let F := silent A b a q
  let E := treeSpace A a
  let f : ((Fin (q+1) → K) × F) →ₗ[K] (Fin s → K) := (coeffEval A q).coprod F.subtype
  let g : ((Fin (q+1) → K) × F) →ₗ[K] E := f.codRestrict E (fun z =>
    E.add_mem ((treeSpace_mono A hq) (coeffEval_mem_treeSpace _ _ _)) (silent_mem.mp z.2.property).1)
  have hg : Function.Injective g := by
    apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    have h : coeffEval A q z.1 + (z.2 : (Fin s → K)) = 0 :=
      congrArg (fun w : E => (w : (Fin s → K))) hz
    have h₁ : z.1=0 := by
      ext i
      apply moments_detect ho (d:=1) (by decide) (by omega) (fun i l => by omega) z.1 _ i
      intro l
      have hh := congrArg (probe A b l.val) h
      rw [map_add, (silent_mem.mp z.2.property).2 l, add_zero,
        probe_coeffEval ho (by omega), map_zero] at hh
      exact hh
    exact Prod.ext h₁ (Subtype.ext (by simpa [h₁] using h))
  simpa only [Module.finrank_prod, Module.finrank_fin_fun] using
    (LinearMap.finrank_le_finrank_of_injective hg)

section Six
variable {A : Matrix (Fin 6) (Fin 6) K} {b : (Fin 6 → K)} {γ : K}

theorem at0 (ha : A.IsLowerTriangular) (he : ∀ i, A i i=γ) (x : (Fin 6 → K)) :
    mat A x 0 = γ*x 0 := by
  change (A *ᵥ x) 0 = _
  rw [lowerTriangular_mulVec_pivot ha 0 x (fun j hj => (Fin.not_lt_zero j hj).elim),he]

theorem at1 (ha : A.IsLowerTriangular) (he : ∀ i, A i i=γ) (x : (Fin 6 → K)) :
    mat A x 1 = A 1 0*x 0+γ*x 1 := by
  have h2:=@ha (1:Fin 6) 2 (by decide); have h3:=@ha (1:Fin 6) 3 (by decide)
  have h4:=@ha (1:Fin 6) 4 (by decide); have h5:=@ha (1:Fin 6) 5 (by decide)
  change (∑ j : Fin 6, A 1 j * x j) = _
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ]
  change _ + (A 1 1*x 1+(A 1 2*x 2+(A 1 3*x 3+(A 1 4*x 4+(A 1 5*x 5+0))))) = _
  rw [he,h2,h3,h4,h5];simp

theorem node_mat_one (A : Matrix (Fin s) (Fin s) K) : nodes A = mat A 1 := by
  rfl

theorem first_tap_nonzero (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular)
    (he : ∀ i, A i i=γ) (hγ : γ≠0) : A 1 0≠0 := by
  intro hv
  have hd (t : FiniteRootedTree) : Φ t A 0 = Φ t A 1 := by
    induction t with
    | leaf => rfl
    | butcherProduct t c ht hc =>
      change Φ t A 0 * mat A (Φ c A) 0 = Φ t A 1 * mat A (Φ c A) 1
      rw [at0 ha he,at1 ha he,hv,zero_mul,zero_add,hc,ht]
  let d := (LinearMap.proj (0:Fin 6) : (Fin 6 → K) →ₗ[K] K) - LinearMap.proj (1:Fin 6)
  have hl : treeSpace A 4≤LinearMap.ker d := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t,_,rfl⟩
    exact sub_eq_zero.mpr (hd t)
  rw [order_six_grade_four_top ho ha (fun i => (he i) ▸ hγ)] at hl
  have hx : ((Pi.single (0:Fin 6) (1:K) : (Fin 6 → K))) ∈ LinearMap.ker d := hl trivial
  change ((Pi.single (0:Fin 6) (1:K) : (Fin 6 → K)) 0) - ((Pi.single (0:Fin 6) (1:K) : (Fin 6 → K)) 1) = 0 at hx
  simp at hx

def seed (A : Matrix (Fin s) (Fin s) K) : (Fin s → K) :=
  (2:K) • mat A (nodes A) - diag (nodes A) (nodes A)

def tapMap (A : Matrix (Fin s) (Fin s) K) (γ : K) : (Fin s → K) →ₗ[K] (Fin s → K) :=
  mat A - γ • LinearMap.id

theorem seed_zero (A : Matrix (Fin s) (Fin s) K) : seed A∈zeroSpace A 2 := by
  have e : seed A = monomialStageDefect A 1 := by
    ext i
    change (2:K)*(A *ᵥ nodes A) i - nodes A i*nodes A i =
      ((1+1:ℕ):K)*(A *ᵥ (nodes A)^1) i - (nodes A i)^(1+1)
    simp [pow_two]
  rw [e]
  exact monomialStageDefect_mem A 1

theorem seed0 (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) : seed A 0=γ^2 := by
  have h : nodes A 0=γ := by rw [node_mat_one,at0 ha he];simp
  change (2:K)*mat A (nodes A) 0-nodes A 0*nodes A 0=_
  rw [at0 ha he,h];ring

theorem tap0 (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (x : (Fin 6 → K)) : tapMap A γ x 0=0 := by
  change mat A x 0-γ*x 0=0;rw [at0 ha he];ring

theorem tap1 (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (x : (Fin 6 → K)) : tapMap A γ x 1=A 1 0*x 0 := by
  change mat A x 1-γ*x 1=_;rw [at1 ha he];ring

theorem tapSeed_zero (ho : HasOrder 6 A b) (γ : K) :
    tapMap A γ (seed A) ∈ zeroSpace A 3 := by
  apply (zeroSpace A 3).sub_mem (mat_zeroSpace ho 2 (by decide) (seed_zero A))
  exact (zeroSpace A 3).smul_mem _ (zeroSpace_mono A (by decide : 2≤3) (seed_zero A))

theorem silent_cubic_rank (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular)
    (he : ∀ i,A i i=γ) (hγ : γ≠0) : Module.finrank K (silent A b 3 2)≤2 := by
  have hr := silent_rank (a:=3) (q:=2) ho (by decide) (by decide)
  have hh := order_six_grade_ranks ho ha (fun i => (he i) ▸ hγ)
  have h₃ := congrArg (fun ls : List ℕ=>ls[3]!) hh
  change Module.finrank K (treeSpace A 3)=5 at h₃
  omega

/-- The first two chronological coordinates determine every silent cubic column. -/
theorem cubic_front_unique (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular)
    (he : ∀ i,A i i=γ) (hγ : γ≠0) (x : (Fin 6 → K))
    (hx : x∈silent A b 3 2) (h0 : x 0=0) (h1 : x 1=0) : x=0 := by
  let S := silent A b 3 2
  let π : S →ₗ[K] (Fin 2→K) := LinearMap.pi (fun j =>
    (LinearMap.proj (j.castLE (by decide : 2≤6))).comp S.subtype)
  have injgrad := silent_cubic_rank ho ha he hγ
  have htap := first_tap_nonzero ho ha he hγ
  have p₀ : seed A ∈ S := zero_le_silent ho (by decide : 3+2+1≤6)
    (zeroSpace_mono A (by decide : 2≤3) (seed_zero A))
  have p₁ : tapMap A γ (seed A) ∈ S := zero_le_silent ho (by decide : 3+2+1≤6) (tapSeed_zero ho γ)
  have sur : Function.Surjective π := by
    intro y
    let a := y 0/γ^2
    let t := (y 1 - a*seed A 1)/(A 1 0*γ^2)
    refine ⟨⟨a • seed A + t • tapMap A γ (seed A), S.add_mem (S.smul_mem _ p₀) (S.smul_mem _ p₁)⟩,?_⟩
    ext j; fin_cases j
    · change a*seed A 0 + t*tapMap A γ (seed A) 0=_
      rw [seed0 ha he,tap0 ha he,mul_zero,add_zero];dsimp [a];field_simp
    · change a*seed A 1 + t*tapMap A γ (seed A) 1=_
      rw [tap1 ha he,seed0 ha he];dsimp [a,t];field_simp;ring
  have lo := LinearMap.finrank_le_finrank_of_surjective sur
  rw [Module.finrank_fin_fun] at lo
  have eqdim : Module.finrank K S=Module.finrank K (Fin 2→K) := by
    rw [Module.finrank_fin_fun];exact le_antisymm injgrad lo
  have inj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank eqdim).mpr sur
  have hπ : π ⟨x,hx⟩=π 0 := by
    rw [map_zero]; ext j;fin_cases j <;> first | exact h0 | exact h1
  exact congrArg (fun z:S => (z:(Fin 6 → K))) (inj hπ)


theorem seed1 (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) :
    seed A 1=γ^2+2*γ*A 1 0-(A 1 0)^2 := by
  have h₀ : nodes A 0=γ := by rw [node_mat_one,at0 ha he];simp
  have h₁ : nodes A 1=A 1 0+γ := by rw [node_mat_one,at1 ha he];simp
  change (2:K)*mat A (nodes A) 1-nodes A 1*nodes A 1=_
  rw [at1 ha he,h₀,h₁];ring

theorem front_clock_seed (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular)
    (he : ∀ i,A i i=γ) (hγ : γ≠0) :
    γ^2 • (diag (nodes A) (seed A) - γ • seed A) =
      seed A 1 • tapMap A γ (seed A) := by
  apply sub_eq_zero.mp
  apply cubic_front_unique ho ha he hγ
  · apply zero_le_silent ho (by decide : 3+2+1≤6)
    apply (zeroSpace A 3).sub_mem
    · apply (zeroSpace A 3).smul_mem
      exact (zeroSpace A 3).sub_mem (diag_zeroSpace A 2 (seed_zero A))
        ((zeroSpace A 3).smul_mem _ (zeroSpace_mono A (by decide : 2≤3) (seed_zero A)))
    · exact (zeroSpace A 3).smul_mem _ (tapSeed_zero ho γ)
  · have h : nodes A 0=γ := by rw [node_mat_one,at0 ha he];simp
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,diag_apply,h,tap0 ha he]; ring
  · have h : nodes A 1=A 1 0+γ := by rw [node_mat_one,at1 ha he];simp
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,diag_apply,h,tap1 ha he,seed0 ha he];ring

theorem comm_one (A : Matrix (Fin s) (Fin s) K) : volterra A 1 = -seed A := by
  have h : diag (nodes A) 1=nodes A := by ext i;simp
  change diag (nodes A) (mat A 1)-mat A (diag (nodes A) 1)-mat A (mat A 1) = _
  rw [← node_mat_one,h]
  ext i;change nodes A i*nodes A i-mat A (nodes A) i-mat A (nodes A) i =
    -((2:K)*mat A (nodes A) i-nodes A i*nodes A i)
  ring

theorem comm0 (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (x : (Fin 6 → K)) :
    volterra A x 0=-(γ^2)*x 0 := by
  rw [volterra_pivot ha 0 x (by intro j h;exact False.elim (Fin.not_lt_zero _ h)),he]

theorem comm1 (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (x : (Fin 6 → K)) :
    volterra A x 1=-(γ^2)*x 1+A 1 0*(nodes A 1-nodes A 0-2*γ)*x 0 := by
  change nodes A 1*mat A x 1 - mat A (diag (nodes A) x) 1 - mat A (mat A x) 1=_
  simp only [at0 ha he,at1 ha he,diag_apply];ring

theorem front_commutator (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular)
    (he : ∀ i,A i i=γ) (hγ : γ≠0) :
    mat A (volterra A 1) = volterra A (mat A 1) := by
  apply sub_eq_zero.mp
  apply cubic_front_unique ho ha he hγ
  · apply (silent A b 3 2).sub_mem
    · rw [comm_one,map_neg]
      exact zero_le_silent ho (by decide : 3+2+1≤6)
        ((zeroSpace A 3).neg_mem (mat_zeroSpace ho 2 (by decide) (seed_zero A)))
    · have hx : mat A (1:(Fin 6 → K))∈treeSpace A 1 := mat_treeSpace A 0 (Φ_mem_treeSpace A .leaf (by decide))
      apply silent_mem.mpr ⟨zeroSpace_le_treeSpace _ _ (volterra_treeSpace ho 1 (by decide) hx),?_⟩
      intro i;exact probe_commutator ho (by omega) hx
  · simp only [Pi.sub_apply,at0 ha he,comm0 ha he,Pi.one_apply];ring
  · simp only [Pi.sub_apply,at1 ha he,at0 ha he,comm1 ha he,comm0 ha he,Pi.one_apply];ring

noncomputable def leg3c (A : Matrix (Fin s) (Fin s) K) : (Fin s → K) := coeffEval A 3 (fun j =>
  if j=0 then -1 else if j=1 then 12 else if j=2 then -30 else 20)

theorem leg3c_at (A : Matrix (Fin s) (Fin s) K) (i : Fin s) :
    leg3c A i = 20*(nodes A i)^3-30*(nodes A i)^2+12*(nodes A i)-1 := by
  simp only [leg3c, coeffEval_apply, normTree_clockTree, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp [Fin.sum_univ_succ]; ring

theorem leg3c_silent [CharZero K] (ho : HasOrder 6 A b) :
    leg3c A∈silent A b 3 2 := by
  apply silent_mem.mpr ⟨coeffEval_mem_treeSpace A 3 _,?_⟩
  intro k
  rw [probe_coeffEval ho (by omega)]
  fin_cases k <;> norm_num [Fin.sum_univ_succ]

theorem cubic_reconstruction (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular)
    (he : ∀ i,A i i=γ) (hγ : γ≠0) (x : (Fin 6 → K)) (hx : x∈silent A b 3 2) :
    x = (x 0/γ^2) • seed A +
      ((x 1 - (x 0/γ^2)*seed A 1)/(A 1 0*γ^2)) • tapMap A γ (seed A) := by
  have hT := first_tap_nonzero ho ha he hγ
  apply sub_eq_zero.mp
  apply cubic_front_unique ho ha he hγ 
  · apply (silent A b 3 2).sub_mem hx
    apply zero_le_silent ho (by decide : 3+2+1≤6)
    exact (zeroSpace A 3).add_mem
      ((zeroSpace A 3).smul_mem _ (zeroSpace_mono A (by decide : 2≤3) (seed_zero A)))
      ((zeroSpace A 3).smul_mem _ (tapSeed_zero ho γ))
  · simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,seed0 ha he,tap0 ha he,
      mul_zero,add_zero]
    field_simp;ring
  · simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,tap1 ha he,seed0 ha he]
    field_simp;ring

end Six
end RKResearch.Certified.Graded.SDIRKSix

