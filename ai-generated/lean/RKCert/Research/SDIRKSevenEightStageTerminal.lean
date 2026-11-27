module
public import RKCert.Research.SDIRKSevenEightStageSigns
public import RKCert.ReviewedNative.SDIRKSixTerminal
public import RKCert.ReviewedNative.ReflectedMoments

@[expose] public section

namespace RKResearch.Certified.Graded.SDIRKSeven
open RKResearch FiniteRootedTree Module Reverse
open SDIRKSix (coord mat_coord diag_coord row_coord probe_coord probe_commutator)
open scoped Matrix

noncomputable section

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 8) (Fin 8) K} {b : Fin 8→K} {γ : K}

private theorem paid_coeff_detect (ho : HasOrder 7 A b) {q : ℕ} (hp : q+q+1≤7)
    (a : Fin (q+1)→K) (hm : ∀ i : Fin (q+1), probe A b i.val (coeffEval A q a)=0) :
    a=0 := by
  ext i
  apply moments_detect ho (d:=1) (by decide) (by omega) (fun i j=>by omega) a _ i
  intro k
  have h := hm k
  rwa [probe_coeffEval ho (by omega)] at h

/-- At equality, the clock/commutator lower-bound injection is onto the actual grade. -/
private theorem actual_comm_frame (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (hn : ∀ i,A i i≠0) (j q : ℕ) (grade : q≤j+2) (pay : q+j+3≤7)
    (hp : q+q+1≤7)
    (dim : finrank K (treeSpace A (j+2)) = q+1+finrank K (treeSpace A j))
    {x : Fin 8→K} (hx : x∈treeSpace A (j+2)) :
    ∃ a : Fin (q+1)→K, ∃ w∈treeSpace A j, x=coeffEval A q a+volterra A w := by
  let F := treeSpace A j
  let E := treeSpace A (j+2)
  let f : ((Fin (q+1)→K) × F) →ₗ[K] (Fin 8→K) :=
    (coeffEval A q).coprod ((volterra A).comp F.subtype)
  let g : ((Fin (q+1)→K) × F) →ₗ[K] E := f.codRestrict E (fun z =>
    E.add_mem (treeSpace_mono A grade (coeffEval_mem_treeSpace _ _ _))
      (zeroSpace_le_treeSpace _ _ (volterra_treeSpace ho j (by omega) z.2.property)))
  have hin : Function.Injective g := by
    apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    have he : coeffEval A q z.1 + volterra A (z.2 : Fin 8→K) = 0 :=
      congrArg (fun w : E => (w : Fin 8→K)) hz
    have s : z.1=0 := paid_coeff_detect ho hp _ (fun i => by
      have h := congrArg (probe A b i.val) he
      rwa [map_add,probe_commutator ho (by omega : i.val+j+3≤7) z.2.property,
        add_zero,map_zero] at h)
    have t : (z.2 : Fin 8→K)=0 := by
      apply (injective_iff_map_eq_zero _).mp (volterra_injective ha hn)
      simpa [s] using he
    exact Prod.ext s (Subtype.ext t)
  have eqdim : finrank K ((Fin (q+1)→K) × F)=finrank K E := by
    simpa only [Module.finrank_prod,Module.finrank_fin_fun] using dim.symm
  have sur := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank eqdim).mp hin
  obtain ⟨z,hz⟩ := sur ⟨x,hx⟩
  exact ⟨z.1,z.2.val,z.2.property,(congrArg (fun r:E => r.val) hz).symm⟩

private theorem invisible_eigenvector_zero (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (hn : ∀ i,A i i≠0) (v : Fin 8→K) (r : K)
    (he : volterra A v=r • v) (tests : ∀ k, probe A b k v=0) : v=0 := by
  have descend (j q : ℕ) (grade : q≤j+2) (pay : q+j+3≤7)
      (hp : q+q+1≤7)
      (hdim : finrank K (treeSpace A (j+2))=q+1+finrank K (treeSpace A j))
      (hv : v∈treeSpace A (j+2)) : v∈treeSpace A j := by
    obtain ⟨a,w,hw,e⟩ := actual_comm_frame ho ha hn j q grade pay hp hdim hv
    have za : a=0 := paid_coeff_detect ho hp _ (fun i => by
      have hh := congrArg (probe A b i.val) e
      rwa [tests,map_add,probe_commutator ho (by omega : i.val+j+3≤7) hw,
        add_zero,eq_comm] at hh)
    have wv : volterra A w=v := by simpa [za] using e.symm
    have hh : v=r • w := volterra_injective ha hn (by rw [he,map_smul,wv])
    rw [hh]
    exact (treeSpace A j).smul_mem _ hw
  have h1 := congrArg (fun xs : List ℕ => xs[1]!) (grade_ranks ho ha hn)
  have h3 := congrArg (fun xs : List ℕ => xs[3]!) (grade_ranks ho ha hn)
  have h5 := congrArg (fun xs : List ℕ => xs[5]!) (grade_ranks ho ha hn)
  change finrank K (treeSpace A 1)=2 at h1
  change finrank K (treeSpace A 3)=6 at h3
  change finrank K (treeSpace A 5)=8 at h5
  have v5 : v∈treeSpace A 5 := by rw [grade_five_top ho ha hn]; trivial
  have v3 := descend 3 1 (by decide) (by decide) (by decide) (by rw [h5,h3]) v5
  have v1 := descend 1 3 (by decide) (by decide) (by decide) (by rw [h3,h1]) v3
  have dd := treeSpace_rank_eq_of_separation ho (q:=1) (by decide) (coeff_separated ho (by decide))
  have zz : zeroSpace A 1 = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    omega
  rw [treeSpace_coeff_sup ho (by decide),zz,sup_bot_eq] at v1
  obtain ⟨a,rfl⟩ := v1
  have za : a=0 := paid_coeff_detect ho (by decide) _ (fun i => tests i.val)
  rw [za,map_zero]

theorem mat_coord_last (ha : A.IsLowerTriangular) (hd : ∀i,A i i=γ) :
    mat A (coord 7)=γ • coord 7 := by
  ext i
  rw [mat_coord]
  by_cases hi : i=7
  · subst i; simp [coord,hd]
  · have hh : i<7 := by change i.val<7; have : i.val≠7 := fun h => hi (Fin.ext h); omega
    simp [@ha i 7 hh,coord,hi]

theorem mat_coord_penultimate (ha : A.IsLowerTriangular) (hd : ∀i,A i i=γ) :
    mat A (coord 6)=γ • coord 6 + A 7 6 • coord 7 := by
  ext i
  rw [mat_coord]
  by_cases h6 : i=6
  · subst i; simp [coord,hd]
  by_cases h7 : i=7
  · subst i; simp [coord]
  · have hh : i<6 := by
      change i.val<6
      have : i.val≠6 := fun h => h6 (Fin.ext h)
      have : i.val≠7 := fun h => h7 (Fin.ext h)
      omega
    simp [@ha i 6 hh,coord,h6,h7]

private theorem comm_mat_eigen (j : Fin 8) (h : mat A (coord j)=γ • coord j) :
    volterra A (coord j)=-(γ^2) • coord j := by
  change diag _ (mat A (coord j)) - mat A (diag _ (coord j)) - mat A (mat A (coord j)) = _
  rw [h,diag_coord]
  simp only [map_smul,diag_coord,h,smul_smul]
  ext i
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring

theorem adjoint_exact (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (hn : ∀ i,A i i≠0) : SDIRKSix.adjResidual A b=0 := by
  apply LinearMap.ext
  intro x
  have hx : x∈treeSpace A 5 := by rw [grade_five_top ho ha hn]; trivial
  exact SDIRKSix.adjResidual_space ho 5 (by decide) hx

/-- No division by weights outside the terminal two rows is used. -/
theorem terminal_chronology (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (hd : ∀ i,A i i=γ) (hγ : γ≠0) :
    b 7≠0 ∧ b 6≠0 ∧ nodes A 7=1-γ ∧ nodes A 7≠nodes A 6 ∧
      b 7*A 7 6=(nodes A 7-nodes A 6)*b 6 := by
  have hn (i) : A i i≠0 := hd i ▸ hγ
  have e7 := comm_mat_eigen (A:=A) 7 (mat_coord_last ha hd)
  have h7 (hz : b 7=0) : False := by
    have h := invisible_eigenvector_zero ho ha hn (coord 7) _ e7
      (fun k => by rw [probe_coord,hz,zero_mul])
    have h' := congrFun h 7
    simp [coord] at h'
  have hD := adjoint_exact ho ha hn
  have h7' := LinearMap.congr_fun hD (coord 7)
  change row b (mat A (coord 7)) + row b (diag _ (coord 7)) - row b (coord 7) = 0 at h7'
  rw [mat_coord_last ha hd,diag_coord,map_smul,map_smul,row_coord,smul_eq_mul,smul_eq_mul] at h7'
  have hc7 : nodes A 7=1-γ := by
    have h : (nodes A 7-(1-γ))*b 7=0 := by linear_combination h7'
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right h7)
  have h6' := LinearMap.congr_fun hD (coord 6)
  change row b (mat A (coord 6)) + row b (diag _ (coord 6)) - row b (coord 6) = 0 at h6'
  rw [mat_coord_penultimate ha hd,diag_coord,map_add,map_smul,map_smul,map_smul,
    row_coord,row_coord,smul_eq_mul,smul_eq_mul,smul_eq_mul] at h6'
  have hlink : b 7*A 7 6=(nodes A 7-nodes A 6)*b 6 := by rw [hc7]; linear_combination h6'
  have e6 (ht : A 7 6=0) : volterra A (coord 6)=-(γ^2) • coord 6 :=
    comm_mat_eigen 6 (by simpa [ht] using mat_coord_penultimate ha hd)
  have h6 (hz : b 6=0) : False := by
    have hl := hlink
    rw [hz,mul_zero] at hl
    have ht := (mul_eq_zero.mp hl).resolve_left h7
    have h := invisible_eigenvector_zero ho ha hn (coord 6) _ (e6 ht)
      (fun k=>by rw [probe_coord,hz,zero_mul])
    have h' := congrFun h 6
    simp [coord] at h'
  refine ⟨h7,h6,hc7,?_,hlink⟩
  intro hc
  have hl := hlink
  rw [hc,sub_self,zero_mul] at hl
  have ht := (mul_eq_zero.mp hl).resolve_left h7
  let v : Fin 8→K := b 7 • coord 6 - b 6 • coord 7
  have hv : volterra A v=-(γ^2) • v := by
    dsimp [v]
    rw [map_sub,map_smul,map_smul,e6 ht,e7,smul_sub]
    ext i
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have hp (k) : probe A b k v=0 := by
    dsimp [v]
    rw [map_sub,map_smul,map_smul,probe_coord,probe_coord,hc]
    change _ * (_*_) - _ * (_*_) = (0:K)
    ring
  have hz := congrFun (invisible_eigenvector_zero ho ha hn v _ hv hp) 6
  exact h7 (by simpa [v,coord] using hz)

/-- The actual weighted quadratic defect and the reflected quadratic
row span the same complementary one-dimensional line when the former
is nonzero. This argument does not invert the full diagonal of weights. -/
theorem terminal_seed_formula (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (hd : ∀ i,A i i=γ) (hγ : γ≠0) :
    (diag b (SDIRKSix.seed A) ≠ 0 → SDIRKSix.seed A 7 ≠ 0) ∧
    γ^2*SDIRKSix.seed A 6 =
      (γ^2+2*γ*(nodes A 7-nodes A 6)-(nodes A 7-nodes A 6)^2)*SDIRKSix.seed A 7 := by
  obtain ⟨h7,h6,hc7,_,hl⟩ := terminal_chronology ho ha hd hγ
  let r := reflectedStageRow A b 1
  let W := annih (treeSpace A 4)
  let Δ := nodes A 7-nodes A 6
  let w := diag b (SDIRKSix.seed A)
  let f : Fin 8→K := fun i => b i*(1-nodes A i)
  have hrW : r∈W := mem_annih.mpr (fun v hv =>
    reflectedStageRow_treeSpace ho 4 1 (by decide) hv)
  have hwW : w∈W := mem_annih.mpr (fun v hv =>
    paid_pair_zero ho (by decide : 2+4+1≤7) (SDIRKSix.seed_zero A) hv)
  have hc6 : 1-nodes A 6 = γ+Δ := by dsimp [Δ]; linear_combination -hc7
  have hc7' : 1-nodes A 7 = γ := by linear_combination -hc7
  have expr (j : Fin 8) : r j =
      (2:K)*row f (mat A (coord j)) - b j*(1-nodes A j)^2 := by
    rw [←row_coord r j]
    change row (reflectedStageRow A b 1) (coord j) = _
    rw [reflectedStageRow_pair, show ((1+1:ℕ):K)=2 by norm_num]
    simp only [reflectedProbe,pow_zero,pow_one,mul_one,reflectedClock,Pi.sub_apply,Pi.one_apply,row_coord]
    rfl
  have rr7 : r 7=b 7*γ^2 := by
    rw [expr,mat_coord_last ha hd,map_smul,smul_eq_mul,row_coord,hc7']
    dsimp only [f]
    rw [hc7']
    ring
  have rr6 : r 6=b 6*(γ^2+2*γ*Δ-Δ^2) := by
    rw [expr,mat_coord_penultimate ha hd,map_add,map_smul,map_smul,
      smul_eq_mul,smul_eq_mul,row_coord,row_coord,hc6]
    dsimp only [f]
    rw [hc6,hc7']
    linear_combination 2*γ*hl
  have r0 : r≠0 := by
    intro e
    have h := congrFun e 7
    rw [rr7] at h
    exact (mul_ne_zero h7 (pow_ne_zero _ hγ)) h
  have d := finrank_annih (treeSpace A 4)
  rw [Fintype.card_fin] at d
  have r4 := congrArg (fun xs : List ℕ => xs[4]!) (grade_ranks ho ha (fun i => hd i ▸ hγ))
  change finrank K (treeSpace A 4)=7 at r4
  have dr : finrank K W=1 := by
    change finrank K (treeSpace A 4)+finrank K W=8 at d
    omega
  have eq : (K ∙ r) = W :=
    Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem r W).mpr hrW)
      (by rw [finrank_span_singleton r0,dr])
  rw [←eq] at hwW
  obtain ⟨μ,hμ⟩ := Submodule.mem_span_singleton.mp hwW
  have q7 := congrFun hμ 7
  change μ*r 7=b 7*SDIRKSix.seed A 7 at q7
  rw [rr7] at q7
  have q7' : μ*γ^2=SDIRKSix.seed A 7 := by
    apply mul_left_cancel₀ h7
    linear_combination q7
  have q6 := congrFun hμ 6
  change μ*r 6=b 6*SDIRKSix.seed A 6 at q6
  rw [rr6] at q6
  have q6' : μ*(γ^2+2*γ*Δ-Δ^2)=SDIRKSix.seed A 6 := by
    apply mul_left_cancel₀ h6
    linear_combination q6
  constructor
  · intro hwn z
    have e : μ=0 := (mul_eq_zero.mp (q7'.trans z)).resolve_right (pow_ne_zero 2 hγ)
    rw [e,zero_smul] at hμ
    exact hwn hμ.symm
  · change γ^2*SDIRKSix.seed A 6 = (γ^2+2*γ*Δ-Δ^2)*SDIRKSix.seed A 7
    rw [←q7',←q6']
    ring

private theorem weighted_cubic_rank_le_one (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (hn : ∀i,A i i≠0) (hm : 0 < (ghostSet b).card) :
    finrank K ((zeroSpace A 3).map (diag b))≤1 := by
  have h := ghost_census ho ha hn
  have r := (grade_three_rank ho ha hn).2
  have z := finrank_map_add_inf_ker (zeroSpace A 3) (diag b)
  rw [←ghostSpace_ker b] at z
  omega

private theorem weighted_seed_clock_unique (ho : HasOrder 7 A b)
    (ha : A.IsLowerTriangular) (hn : ∀i,A i i≠0)
    (hm : 0 < (ghostSet b).card) (h : diag b (SDIRKSix.seed A)≠0) :
    ∃ x : K, ∀ i, b i≠0 → SDIRKSix.seed A i≠0 → nodes A i=x := by
  let V := (zeroSpace A 3).map (diag b)
  let w := diag b (SDIRKSix.seed A)
  have hw : w∈V := Submodule.mem_map_of_mem (zeroSpace_mono A (by decide : 2≤3) (SDIRKSix.seed_zero A))
  have hcw : diag b (diag (nodes A) (SDIRKSix.seed A))∈V :=
    Submodule.mem_map_of_mem (diag_zeroSpace A 2 (SDIRKSix.seed_zero A))
  have eq : (K ∙ w)=V :=
    Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem w V).mpr hw)
      (by rw [finrank_span_singleton h]; exact weighted_cubic_rank_le_one ho ha hn hm)
  rw [←eq] at hcw
  obtain ⟨x,e⟩ := Submodule.mem_span_singleton.mp hcw
  refine ⟨x,fun i hb hg => ?_⟩
  have z := congrFun e i
  change x*(b i*SDIRKSix.seed A i)=b i*(nodes A i*SDIRKSix.seed A i) at z
  apply mul_right_cancel₀ (mul_ne_zero hb hg)
  linear_combination -z

private theorem sqrt_two_of_seed_eq_zero {q : K} (hγ : γ≠0)
    (h : γ^2+2*γ*q-q^2=0) : IsSquare (2:K) := by
  refine ⟨q/γ-1,?_⟩
  field_simp
  linear_combination h

/-- Over a field without a square root of two, any ghost forces *all*
paid cubic defects to vanish on the active stages, irrespective of
clock collisions or the signs of weights. -/
theorem cubic_hidden_of_ghost_no_sqrt_two (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (hd : ∀ i,A i i=γ) (hγ : γ≠0) (h₂ : ¬ IsSquare (2:K))
    (hm : 0 < (ghostSet b).card) : zeroSpace A 3 ≤ ghostSpace b := by
  have w0 : diag b (SDIRKSix.seed A)=0 := by
    by_contra hw
    obtain ⟨hb7,hb6,_,hc,_⟩ := terminal_chronology ho ha hd hγ
    obtain ⟨h7r,ratio⟩ := terminal_seed_formula ho ha hd hγ
    have h7 := h7r hw
    obtain ⟨x,hx⟩ := weighted_seed_clock_unique ho ha (fun i=>hd i ▸ hγ) hm hw
    have h6 : SDIRKSix.seed A 6=0 := by
      by_contra e
      exact hc ((hx 7 hb7 h7).trans (hx 6 hb6 e).symm)
    rw [h6,mul_zero] at ratio
    have z := (mul_eq_zero.mp ratio.symm).resolve_right h7
    exact h₂ (sqrt_two_of_seed_eq_zero hγ z)
  have s1 : SDIRKSix.seed A 1 ≠ 0 := by
    intro e
    rw [seed₁ ha hd] at e
    exact h₂ (sqrt_two_of_seed_eq_zero hγ e)
  intro v hv
  let a := v 0/γ^2
  let t := (v 1-a*SDIRKSix.seed A 1)/(A 1 0*γ^2)
  let gv := SDIRKSix.seed A
  let Ng := SDIRKSix.tapMap A γ gv
  have hg : gv ∈ zeroSpace A 3 := zeroSpace_mono A (by decide : 2≤3) (SDIRKSix.seed_zero A)
  have hNg : Ng∈zeroSpace A 3 := tap_seed_zero ho
  have ht := first_tap_ne_zero ho ha hd hγ
  have rep : v=a • gv+t • Ng := by
    apply sub_eq_zero.mp
    apply cubic_head_unique ho ha hd hγ
    · exact (zeroSpace A 3).sub_mem hv ((zeroSpace A 3).add_mem
        ((zeroSpace A 3).smul_mem _ hg) ((zeroSpace A 3).smul_mem _ hNg))
    · have hNg0 : Ng 0=0 := tap₀ ha hd gv
      simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,gv,seed₀ ha hd,hNg0,mul_zero,add_zero]
      dsimp [a]
      field_simp
      ring
    · have ht₁ : Ng 1=A 1 0*γ^2 := by
        change SDIRKSix.tapMap A γ gv 1=A 1 0*γ^2
        rw [tap₁ ha hd,show gv 0=γ^2 from seed₀ ha hd]
      simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,ht₁,gv]
      dsimp [t,a]
      field_simp
      ring
  apply mem_ghostSpace.mpr
  intro i bi
  have gv0 : gv i=0 := (mul_eq_zero.mp (congrFun w0 i)).resolve_left bi
  have e := congrFun (cubic_seed_clock ho ha hd hγ) i
  change γ^2*(nodes A i*gv i-γ*gv i)=SDIRKSix.seed A 1*Ng i at e
  rw [gv0,mul_zero,mul_zero,sub_self,mul_zero] at e
  have Ng0 := (mul_eq_zero.mp e.symm).resolve_left s1
  rw [rep]
  change a*gv i+t*Ng i=0
  rw [gv0,Ng0,mul_zero,mul_zero,add_zero]

end
end RKResearch.Certified.Graded.SDIRKSeven
