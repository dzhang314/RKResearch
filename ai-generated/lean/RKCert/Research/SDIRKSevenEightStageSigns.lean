module
public import RKCert.ReviewedNative.SDIRKSixFront
public import RKCert.ReviewedNative.GradedProducts
public import RKCert.ReviewedNative.RowAnnihilator
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity

@[expose] public section

/-! # The paid midpoint and the physical zero-weight cut at eight stages -/

namespace RKResearch.Certified.Graded.SDIRKSeven
open RKResearch FiniteRootedTree Module Reverse
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 8) (Fin 8) K} {b : Fin 8 → K} {γ : K}

theorem grade_ranks (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (hn : ∀ i, A i i ≠ 0) :
    (List.range 7).map (fun j => finrank K (treeSpace A j)) = [1,2,4,6,7,8,8] := by
  let v := fun j => finrank K (treeSpace A j)
  have up (j : ℕ) : v j ≤ 8 := by
    simpa only [v, Module.finrank_fin_fun] using Submodule.finrank_le (treeSpace A j)
  have low (j : ℕ) (hp : j+1≤7) := parityCensus_le_finrank ho ha hn j hp
  have h₀ := low 0 (by decide); have h₁ := low 1 (by decide); have h₂ := low 2 (by decide)
  have h₃ := low 3 (by decide); have h₄ := low 4 (by decide); have h₅ := low 5 (by decide)
  have h₆ := low 6 (by decide)
  change 1≤v 0 at h₀; change 2≤v 1 at h₁; change 4≤v 2 at h₂; change 6≤v 3 at h₃
  change 7≤v 4 at h₄; change 8≤v 5 at h₅; change 8≤v 6 at h₆
  have e₀ := nonsingular_rank_step ho ha hn 0 2 (by decide) (by decide)
  have e₁ := nonsingular_rank_step ho ha hn 1 3 (by decide) (by decide)
  have e₂ := nonsingular_rank_step ho ha hn 2 2 (by decide) (by decide)
  have e₃ := nonsingular_rank_step ho ha hn 3 1 (by decide) (by decide)
  have e₄ := nonsingular_rank_step ho ha hn 4 0 (by decide) (by decide)
  change 3+v 0≤v 2 at e₀; change 4+v 1≤v 3 at e₁; change 3+v 2≤v 4 at e₂
  change 2+v 3≤v 5 at e₃; change 1+v 4≤v 6 at e₄
  have u₄ := up 4; have u₅ := up 5; have u₆ := up 6
  change [v 0,v 1,v 2,v 3,v 4,v 5,v 6] = _
  rw [show v 0=1 by omega, show v 1=2 by omega, show v 2=4 by omega, show v 3=6 by omega,
    show v 4=7 by omega, show v 5=8 by omega, show v 6=8 by omega]

theorem grade_three_rank (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (hn : ∀ i, A i i ≠ 0) :
    finrank K (treeSpace A 3) = 6 ∧ finrank K (zeroSpace A 3) = 2 := by
  have e := congrArg (fun xs : List ℕ => xs[3]!) (grade_ranks ho ha hn)
  change finrank K (treeSpace A 3) = 6 at e
  have f := treeSpace_rank_eq_of_separation ho (q:=3) (by decide) (coeff_separated ho (by decide))
  exact ⟨e, by omega⟩

theorem grade_five_top (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (hn : ∀ i, A i i ≠ 0) : treeSpace A 5 = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have h := congrArg (fun xs : List ℕ => xs[5]!) (grade_ranks ho ha hn)
  change finrank K (treeSpace A 5)=8 at h
  simpa only [Module.finrank_fin_fun] using h

theorem cubic_silent_eq (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (hn : ∀ i, A i i ≠ 0) : SDIRKSix.silent A b 3 3 = zeroSpace A 3 := by
  symm
  apply Submodule.eq_of_le_of_finrank_le (SDIRKSix.zero_le_silent ho (by decide))
  have h := SDIRKSix.silent_rank ho (a:=3) (q:=3) (by decide) (by decide)
  obtain ⟨e,f⟩ := grade_three_rank ho ha hn
  omega

theorem head₀ (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (x : Fin 8 → K) :
    mat A x 0 = γ*x 0 := by
  change (A *ᵥ x) 0 = _
  rw [lowerTriangular_mulVec_pivot ha 0 x (fun _ hj => (Fin.not_lt_zero _ hj).elim),he]

theorem head₁ (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (x : Fin 8 → K) :
    mat A x 1 = A 1 0*x 0+γ*x 1 := by
  change (∑ j : Fin 8, A 1 j * x j) = _
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  change A 1 0*x 0+(A 1 1*x 1+∑ j : Fin 6, A 1 j.succ.succ*x j.succ.succ) = _
  have hz : (∑ j : Fin 6, A 1 j.succ.succ*x j.succ.succ) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have e : (1 : Fin 8) < j.succ.succ := by
      change 1 < j.val+1+1
      omega
    have z : A 1 j.succ.succ=0 := @ha (1:Fin 8) j.succ.succ e
    exact mul_eq_zero.mpr (Or.inl z)
  rw [hz,he,add_zero]

theorem first_tap_ne_zero (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (he : ∀ i,A i i=γ) (hγ : γ≠0) : A 1 0≠0 := by
  intro hv
  have hd (t : FiniteRootedTree) : Φ t A 0 = Φ t A 1 := by
    induction t with
    | leaf => rfl
    | butcherProduct t c ht hc =>
      change Φ t A 0 * mat A (Φ c A) 0 = Φ t A 1 * mat A (Φ c A) 1
      rw [head₀ ha he,head₁ ha he,hv,zero_mul,zero_add,hc,ht]
  let d := (LinearMap.proj (0:Fin 8) : (Fin 8→K) →ₗ[K] K) - LinearMap.proj (1:Fin 8)
  have hl : treeSpace A 5≤LinearMap.ker d := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t,_,rfl⟩
    exact sub_eq_zero.mpr (hd t)
  rw [grade_five_top ho ha (fun i => he i ▸ hγ)] at hl
  have hx : (coordinate (K:=K) (0:Fin 8)) ∈ LinearMap.ker d := hl trivial
  replace hx := LinearMap.mem_ker.mp hx
  have z : coordinate (K:=K) (0:Fin 8) 0 - coordinate (K:=K) (0:Fin 8) 1 = 0 := by
    simpa only [d,LinearMap.sub_apply,LinearMap.proj_apply] using hx
  simp [coordinate] at z

theorem clock₀ (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) : nodes A 0=γ := by
  rw [SDIRKSix.node_mat_one, head₀ ha he]; simp

theorem clock₁ (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) : nodes A 1=A 1 0+γ := by
  rw [SDIRKSix.node_mat_one, head₁ ha he]; simp

theorem seed₀ (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) : SDIRKSix.seed A 0=γ^2 := by
  change (2:K)*mat A (nodes A) 0-nodes A 0*nodes A 0=_
  rw [head₀ ha he,clock₀ ha he]; ring

theorem seed₁ (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) :
    SDIRKSix.seed A 1=γ^2+2*γ*A 1 0-(A 1 0)^2 := by
  change (2:K)*mat A (nodes A) 1-nodes A 1*nodes A 1=_
  rw [head₁ ha he,clock₀ ha he,clock₁ ha he]; ring

theorem tap₀ (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (x : Fin 8 → K) :
    SDIRKSix.tapMap A γ x 0=0 := by
  change mat A x 0-γ*x 0=0; rw [head₀ ha he]; ring

theorem tap₁ (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (x : Fin 8 → K) :
    SDIRKSix.tapMap A γ x 1=A 1 0*x 0 := by
  change mat A x 1-γ*x 1=_; rw [head₁ ha he]; ring

theorem tap_seed_zero (ho : HasOrder 7 A b) :
    SDIRKSix.tapMap A γ (SDIRKSix.seed A) ∈ zeroSpace A 3 := by
  apply (zeroSpace A 3).sub_mem (mat_zeroSpace ho 2 (by decide) (SDIRKSix.seed_zero A))
  exact (zeroSpace A 3).smul_mem _ (zeroSpace_mono A (by decide : 2≤3) (SDIRKSix.seed_zero A))

/-- Saturated cubic defects are detected by the first two physical rows. -/
theorem cubic_head_unique (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (he : ∀ i,A i i=γ) (hγ : γ≠0) {x : Fin 8 → K}
    (hx : x ∈ zeroSpace A 3) (h₀ : x 0=0) (h₁ : x 1=0) : x=0 := by
  let S := zeroSpace A 3
  let π : S →ₗ[K] (Fin 2→K) := LinearMap.pi (fun j =>
    (LinearMap.proj (j.castLE (by decide : 2≤8))).comp S.subtype)
  have hr := (grade_three_rank ho ha (fun i => he i ▸ hγ)).2
  have ht := first_tap_ne_zero ho ha he hγ
  have p₀ : SDIRKSix.seed A ∈ S := zeroSpace_mono A (by decide : 2≤3) (SDIRKSix.seed_zero A)
  have p₁ : SDIRKSix.tapMap A γ (SDIRKSix.seed A) ∈ S := tap_seed_zero ho
  have sur : Function.Surjective π := by
    intro y
    let a := y 0/γ^2
    let t := (y 1-a*SDIRKSix.seed A 1)/(A 1 0*γ^2)
    refine ⟨⟨a • SDIRKSix.seed A + t • SDIRKSix.tapMap A γ (SDIRKSix.seed A),
      S.add_mem (S.smul_mem _ p₀) (S.smul_mem _ p₁)⟩,?_⟩
    ext j; fin_cases j
    · change a*SDIRKSix.seed A 0+t*SDIRKSix.tapMap A γ (SDIRKSix.seed A) 0=_
      rw [seed₀ ha he,tap₀ ha he,mul_zero,add_zero]; dsimp [a]; field_simp
    · change a*SDIRKSix.seed A 1+t*SDIRKSix.tapMap A γ (SDIRKSix.seed A) 1=_
      rw [tap₁ ha he,seed₀ ha he]; dsimp [a,t]; field_simp; ring
  have eqdim : finrank K S=finrank K (Fin 2→K) := by simpa using hr
  have inj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank eqdim).mpr sur
  have hπ : π ⟨x,hx⟩=π 0 := by
    rw [map_zero]; ext j; fin_cases j <;> first | exact h₀ | exact h₁
  exact congrArg (fun z:S => (z:Fin 8→K)) (inj hπ)

theorem cubic_seed_clock (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (he : ∀ i,A i i=γ) (hγ : γ≠0) :
    γ^2 • (diag (nodes A) (SDIRKSix.seed A) - γ • SDIRKSix.seed A) =
      SDIRKSix.seed A 1 • SDIRKSix.tapMap A γ (SDIRKSix.seed A) := by
  apply sub_eq_zero.mp
  apply cubic_head_unique ho ha he hγ
  · apply (zeroSpace A 3).sub_mem
    · apply (zeroSpace A 3).smul_mem
      exact (zeroSpace A 3).sub_mem (diag_zeroSpace A 2 (SDIRKSix.seed_zero A))
        ((zeroSpace A 3).smul_mem _ (zeroSpace_mono A (by decide : 2≤3) (SDIRKSix.seed_zero A)))
    · exact (zeroSpace A 3).smul_mem _ (tap_seed_zero ho)
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, diag_apply, clock₀ ha he, tap₀ ha he]
    ring
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, diag_apply, clock₁ ha he, tap₁ ha he,seed₀ ha he]
    ring

section Support
variable {ι : Type*} [Fintype ι]

/-- Coordinate subspace on a literal finite set of stages. -/
def onCoordinates (S : Finset ι) : Submodule K (ι→K) :=
  { carrier := {x | ∀ i ∉ S, x i = 0}
    zero_mem' := fun _ _ => rfl
    add_mem' := fun hx hy i hi => by simp [hx i hi,hy i hi]
    smul_mem' := fun a _ hx i hi => by simp [hx i hi] }

omit [Fintype ι] in
theorem mem_onCoordinates {S : Finset ι} {x : ι→K} :
    x ∈ onCoordinates S ↔ ∀ i ∉ S, x i=0 := Iff.rfl

omit [Fintype ι] in
theorem finrank_onCoordinates (S : Finset ι) :
    finrank K (onCoordinates S : Submodule K (ι→K)) = S.card := by
  classical
  let f : (onCoordinates S : Submodule K (ι→K)) ≃ₗ[K] (S→K) :=
    { toFun := fun x i => x.val i.val
      invFun := fun y => ⟨fun i => if hi : i∈S then y ⟨i,hi⟩ else 0,
        mem_onCoordinates.mpr (fun i hi => dite_eq_right hi)⟩
      left_inv := fun x => Subtype.ext (funext (fun i => by
        by_cases hi : i∈S
        · exact dite_eq_left hi
        · exact (dite_eq_right hi).trans ((mem_onCoordinates.mp x.property) i hi).symm))
      right_inv := fun y => funext (fun i => dite_eq_left i.property)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [f.finrank_eq,Module.finrank_fintype_fun_eq_card,Fintype.card_coe]

end Support

def ghostSet (b : Fin 8→K) : Finset (Fin 8) := by
  classical
  exact Finset.univ.filter (fun i => b i=0)

theorem mem_ghostSet {i : Fin 8} : i∈ghostSet b ↔ b i=0 := by simp [ghostSet]

def ghostSpace (b : Fin 8→K) : Submodule K (Fin 8→K) := onCoordinates (ghostSet b)

theorem mem_ghostSpace {x : Fin 8→K} :
    x∈ghostSpace b ↔ ∀ i, b i≠0 → x i=0 := by
  rw [ghostSpace,mem_onCoordinates]
  simp only [mem_ghostSet]

theorem ghostSpace_ker (b : Fin 8→K) : ghostSpace b = (diag b).ker := by
  ext x
  rw [mem_ghostSpace,LinearMap.mem_ker]
  constructor
  · intro h
    ext i
    change b i*x i=0
    by_cases z : b i=0
    · rw [z,zero_mul]
    · rw [h i z,mul_zero]
  · intro h i bi
    exact (mul_eq_zero.mp (congrFun h i)).resolve_left bi

theorem ghostSpace_rank (b : Fin 8→K) :
    finrank K (ghostSpace b) = (ghostSet b).card :=
  finrank_onCoordinates _

private theorem row_eq_probe (x : Fin 8→K) : row b x = probe A b 0 x := by
  simp [probe,dotProduct]

theorem paid_pair_zero (ho : HasOrder 7 A b) {m n : ℕ}
    (h : m+n+1≤7) {x y : Fin 8→K} (hx : x ∈ zeroSpace A m) (hy : y ∈ treeSpace A n) :
    row (diag b x) y=0 := by
  have z := zeroSpace_mul_treeSpace ho (by omega : n+1≤7) hx hy
  have e := probe_zeroSpace ho (k:=0) (by omega : 0+(m+n)+1≤7) z
  have eq : row (diag b x) y = row b (x*y) := by
    simp only [row_apply,dotProduct,diag_apply,Pi.mul_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rwa [eq,row_eq_probe (A:=A)]

private theorem ghost_row_zero {x y : Fin 8→K} (hy : y∈ghostSpace b) :
    row (diag b x) y=0 := by
  simp only [row_apply,dotProduct,diag_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases z : b i=0
  · rw [z,zero_mul,zero_mul]
  · rw [mem_ghostSpace.mp hy i z,mul_zero]

theorem midpoint_ghost_eq (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (hn : ∀ i, A i i≠0) :
    (treeSpace A 3 ⊓ ghostSpace b) = (zeroSpace A 3 ⊓ ghostSpace b) := by
  apply le_antisymm _ (inf_le_inf_right _ (zeroSpace_le_treeSpace A 3))
  intro x hx
  rcases Submodule.mem_inf.mp hx with ⟨hx,hg⟩
  refine Submodule.mem_inf.mpr ⟨?_,hg⟩
  rw [←cubic_silent_eq ho ha hn]
  refine SDIRKSix.silent_mem.mpr ⟨hx,fun i => ?_⟩
  simp only [probe,row_apply,dotProduct]
  apply Finset.sum_eq_zero
  intro t _
  by_cases ht : b t=0
  · simp [ht]
  · simp [mem_ghostSpace.mp hg t ht]

theorem finrank_map_add_inf_ker (F : Submodule K (Fin 8→K))
    (f : (Fin 8→K) →ₗ[K] (Fin 8→K)) :
    finrank K (F.map f) + finrank K ↥(F ⊓ f.ker) = finrank K F := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.comp F.subtype)
  have range : (f.comp F.subtype).range = F.map f := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨x.val,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
  have ker : ((f.comp F.subtype).ker).map F.subtype = (F ⊓ f.ker) := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨x.property,LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp hx)⟩
    · intro hy
      exact ⟨⟨y,hy.1⟩,LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp hy.2),rfl⟩
  rw [range] at h
  rw [←ker,Submodule.finrank_map_subtype_eq]
  exact h

/-- Two zero weights cost at least one ghost-supported cubic defect. This
holds over every field allowing the order, without signs. -/
theorem ghost_census (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (hn : ∀ i, A i i≠0) :
    (ghostSet b).card ≤ 2 * finrank K ↥(zeroSpace A 3 ⊓ ghostSpace b) := by
  let F := zeroSpace A 3
  let E := treeSpace A 3
  let U := ghostSpace b
  have Ef := grade_three_rank ho ha hn
  have eq : (E ⊓ U) = (F ⊓ U) := midpoint_ghost_eq ho ha hn
  have rkU : finrank K U = (ghostSet b).card := ghostSpace_rank b
  have rk := finrank_map_add_inf_ker F (diag b)
  rw [←ghostSpace_ker b] at rk
  change finrank K (F.map (diag b)) + finrank K ↥(F⊓U) = finrank K F at rk
  have inc : F.map (diag b) ≤ annih (E ⊔ U) := by
    rintro _ ⟨x,hx,rfl⟩
    apply mem_annih.mpr
    intro w hw
    obtain ⟨a,hae,u,hu,rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add, paid_pair_zero ho (by decide : 3+3+1≤7) hx hae,ghost_row_zero hu,add_zero]
  have a := Submodule.finrank_mono inc
  have d := finrank_annih (E ⊔ U)
  rw [Fintype.card_fin] at d
  have s := Submodule.finrank_sup_add_finrank_inf_eq E U
  rw [eq] at s
  change finrank K E=6 ∧ finrank K F=2 at Ef
  change (ghostSet b).card ≤ 2 * finrank K ↥(F ⊓ U)
  omega

theorem ghosts_at_most_four (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (hn : ∀ i, A i i≠0) : (ghostSet b).card ≤ 4 := by
  have r := (grade_three_rank ho ha hn).2
  have le := Submodule.finrank_mono
    (inf_le_left : zeroSpace A 3 ⊓ ghostSpace b ≤ zeroSpace A 3)
  have lr := ghost_census ho ha hn
  omega

/-- No ghost mask can start after the first two physical stages. -/
theorem ghost_at_front (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (he : ∀ i,A i i=γ) (hγ : γ≠0) (hm : 0 < (ghostSet b).card) :
    b 0=0 ∨ b 1=0 := by
  by_contra hz
  push Not at hz
  have no : (zeroSpace A 3 ⊓ ghostSpace b) = ⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    have hv₀ := mem_ghostSpace.mp hv.2 0 hz.1
    have hv₁ := mem_ghostSpace.mp hv.2 1 hz.2
    rw [cubic_head_unique ho ha he hγ hv.1 hv₀ hv₁]
    exact Submodule.zero_mem _
  have r := ghost_census ho ha (fun i => he i ▸ hγ)
  rw [no,finrank_bot] at r
  omega

theorem cubic_hidden_of_three_ghosts (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (hn : ∀ i,A i i≠0) (hm : 3 ≤ (ghostSet b).card) :
    zeroSpace A 3 ≤ ghostSpace b := by
  have lo := ghost_census ho ha hn
  have r := (grade_three_rank ho ha hn).2
  have eq : (zeroSpace A 3 ⊓ ghostSpace b) = zeroSpace A 3 :=
    Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
  rw [← inf_eq_left]
  exact eq

/-- Three or more ghosts force both head rows, and no active row has a
nonzero cubic defect. The same two conclusions hold whenever all cubic
defects are hidden, e.g. with nonnegative weights. -/
theorem both_front_ghosts_of_cubic_hidden (ho : HasOrder 7 A b)
    (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (hγ : γ≠0)
    (hidden : zeroSpace A 3 ≤ ghostSpace b) : b 0=0 ∧ b 1=0 := by
  constructor
  · by_contra hnz
    have e := mem_ghostSpace.mp (hidden
      (zeroSpace_mono A (by decide : 2≤3) (SDIRKSix.seed_zero A))) 0 hnz
    rw [seed₀ ha he] at e
    exact (pow_ne_zero _ hγ) e
  · by_contra hnz
    have e := mem_ghostSpace.mp (hidden (tap_seed_zero (γ:=γ) ho)) 1 hnz
    rw [tap₁ ha he,seed₀ ha he] at e
    exact (mul_ne_zero (first_tap_ne_zero ho ha he hγ) (pow_ne_zero _ hγ)) e

section Ordered
variable [LinearOrder K] [IsStrictOrderedRing K]

def negativeSet (b : Fin 8→K) : Finset (Fin 8) :=
  Finset.univ.filter (fun i => b i<0)

private def nonpositiveSet (b : Fin 8→K) : Finset (Fin 8) :=
  Finset.univ.filter (fun i => b i≤0)

private def nonnegativeSet (b : Fin 8→K) : Finset (Fin 8) :=
  Finset.univ.filter (fun i => 0≤b i)

omit [IsStrictOrderedRing K] in
private theorem neg_card_add_ghost :
    (negativeSet b).card + (ghostSet b).card = (nonpositiveSet b).card := by
  have dj : Disjoint (negativeSet b) (ghostSet b) := by
    apply Finset.disjoint_left.mpr
    intro i hn hz
    exact (Finset.mem_filter.mp hn).2.ne (mem_ghostSet.mp hz)
  have e : negativeSet b ∪ ghostSet b = nonpositiveSet b := by
    ext i
    simp [negativeSet,mem_ghostSet,nonpositiveSet,le_iff_lt_or_eq]
  rw [←e,Finset.card_union_of_disjoint dj]

omit [IsStrictOrderedRing K] in
private theorem neg_card_add_nonnegative :
    (negativeSet b).card + (nonnegativeSet b).card = 8 := by
  classical
  simpa only [negativeSet,nonnegativeSet,not_lt,Finset.card_univ,Fintype.card_fin] using
    (Finset.card_filter_add_card_filter_not (s:=Finset.univ) (fun i : Fin 8 => b i<0))

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem weighted_square_expansion (x : Fin 8→K) :
    row (diag b x) x = ∑ i, b i*(x i*x i) := by
  simp only [row_apply,dotProduct,diag_apply,mul_assoc]

private theorem square_clock_gram (ho : HasOrder 7 A b) (a : Fin 4→K) :
    row (diag b (coeffEval A 3 a)) (coeffEval A 3 a) =
      (a 0 + a 1/2 + a 2/3 + a 3/4)^2 +
      (a 1/2 + a 2/2 + 9*(a 3)/20)^2/3 +
      (a 2/6 + a 3/4)^2/5 +
      (a 3/20)^2/7 := by
  have h (v : Fin 8→K) :
      row (diag b v) (coeffEval A 3 a) = ∑ j:Fin 4, a j * probe A b j.val v := by
    rw [coeffEval_apply,map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul,normTree_clockTree]
    congr 1
    simp only [probe,row_apply,dotProduct,diag_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h]
  have hp (j : Fin 4) := probe_coeffEval ho (k:=j.val) (q:=3) (by have := j.isLt; omega) a
  simp_rw [hp]
  norm_num [Fin.sum_univ_succ]; ring

private theorem midpoint_square_nonnegative (ho : HasOrder 7 A b)
    {x : Fin 8→K} (hx : x∈treeSpace A 3) :
    0 ≤ row (diag b x) x := by
  rw [treeSpace_coeff_sup ho (by decide)] at hx
  obtain ⟨u,⟨a,rfl⟩,v,hv,rfl⟩ := Submodule.mem_sup.mp hx
  let u := coeffEval A 3 a
  have hu : u∈treeSpace A 3 := coeffEval_mem_treeSpace _ _ _
  have hz₁ : row (diag b v) u=0 := paid_pair_zero ho (by decide : 3+3+1≤7) hv hu
  have hz₂ : row (diag b u) v=0 := by
    calc
      row (diag b u) v = row (diag b v) u := by
        simp only [row_apply,dotProduct,diag_apply]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = 0 := hz₁
  have hz₃ : row (diag b v) v=0 :=
    paid_pair_zero ho (by decide : 3+3+1≤7) hv (zeroSpace_le_treeSpace _ _ hv)
  change 0 ≤ row (diag b (u+v)) (u+v)
  have hh : row (diag b (u+v)) (u+v) = row (diag b u) u := by
    change diag b (u+v) ⬝ᵥ (u+v) = diag b u ⬝ᵥ u
    simp only [map_add,add_dotProduct,dotProduct_add]
    simp only [row_apply] at hz₁ hz₂ hz₃
    rw [hz₁,hz₂,hz₃]
    simp
  rw [hh]
  unfold u
  rw [square_clock_gram ho]
  positivity

private theorem ghost_of_nonnegative_mask_square_zero {x : Fin 8→K}
    (hx : x∈onCoordinates (nonnegativeSet b)) (hs : row (diag b x) x=0) :
    x∈ghostSpace b := by
  rw [weighted_square_expansion] at hs
  have hnon (i : Fin 8) : 0 ≤ b i*(x i*x i) := by
    by_cases hi : 0≤b i
    · exact mul_nonneg hi (mul_self_nonneg _)
    · have h0 := mem_onCoordinates.mp hx i (by simpa [nonnegativeSet] using hi)
      simp [h0]
  have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnon i)).mp hs
  apply mem_ghostSpace.mpr
  intro i hi
  have zi := (mul_eq_zero.mp (h i (Finset.mem_univ _))).resolve_left hi
  exact (mul_eq_zero.mp zi).elim id id

private theorem ghost_of_nonpositive_mask_square_nonneg {x : Fin 8→K}
    (hx : x∈onCoordinates (nonpositiveSet b)) (hs : 0≤row (diag b x) x) :
    x∈ghostSpace b := by
  have hnon (i : Fin 8) : 0 ≤ -(b i*(x i*x i)) := by
    by_cases hi : b i≤0
    · exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg hi (mul_self_nonneg _))
    · have h0 := mem_onCoordinates.mp hx i (by simpa [nonpositiveSet] using hi)
      simp [h0]
  have es : ∑ i, -(b i*(x i*x i)) = 0 := by
    rw [Finset.sum_neg_distrib,←weighted_square_expansion]
    exact neg_eq_zero.mpr (le_antisymm (neg_nonneg.mp (by
      rw [weighted_square_expansion,←Finset.sum_neg_distrib]
      exact Finset.sum_nonneg (fun i _ => hnon i))) hs)
  have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnon i)).mp es
  apply mem_ghostSpace.mpr
  intro i hi
  have zi := (mul_eq_zero.mp (neg_eq_zero.mp (h i (Finset.mem_univ _)))).resolve_left hi
  exact (mul_eq_zero.mp zi).elim id id

/-- Let d be the dimension of cubic defects supported only at zero
weights. There must be at least 2-d negative weights, and at most
2+d-m, with m the number of zero weights. No distinct-clock or
nonzero-weight assumption; only ordered-field arithmetic. -/
theorem signed_ghost_census (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (hn : ∀ i,A i i≠0) :
    2 ≤ (negativeSet b).card + finrank K ↥(zeroSpace A 3 ⊓ ghostSpace b) ∧
    (negativeSet b).card + (ghostSet b).card ≤ 2 + finrank K ↥(zeroSpace A 3 ⊓ ghostSpace b) := by
  let E := treeSpace A 3
  let F := zeroSpace A 3
  let U := ghostSpace b
  let V := onCoordinates (nonnegativeSet b) (K:=K)
  let W := onCoordinates (nonpositiveSet b) (K:=K)
  have r := grade_three_rank ho ha hn
  have hV : U≤V := by
    intro x hx
    apply mem_onCoordinates.mpr
    intro i hi
    apply mem_ghostSpace.mp hx i
    intro z
    exact hi (by simp [nonnegativeSet,z])
  have hW : U≤W := by
    intro x hx
    apply mem_onCoordinates.mpr
    intro i hi
    apply mem_ghostSpace.mp hx i
    intro z
    exact hi (by simp [nonpositiveSet,z])
  have eV : (F ⊓ V) = (F ⊓ U) := by
    apply le_antisymm _ (inf_le_inf_left F hV)
    intro x hx
    have hs := paid_pair_zero ho (by decide : 3+3+1≤7) hx.1 (zeroSpace_le_treeSpace _ _ hx.1)
    exact ⟨hx.1,ghost_of_nonnegative_mask_square_zero hx.2 hs⟩
  have eW : (E ⊓ W) = (F ⊓ U) := by
    rw [←midpoint_ghost_eq ho ha hn]
    apply le_antisymm _ (inf_le_inf_left E hW)
    intro x hx
    exact ⟨hx.1,ghost_of_nonpositive_mask_square_nonneg hx.2 (midpoint_square_nonnegative ho hx.1)⟩
  have aV := Submodule.finrank_sup_add_finrank_inf_eq F V
  have aW := Submodule.finrank_sup_add_finrank_inf_eq E W
  have cap (S : Submodule K (Fin 8→K)) : finrank K S≤8 := by simpa using Submodule.finrank_le S
  have cV := cap (F⊔V)
  have cW := cap (E⊔W)
  rw [eV, show finrank K V = (nonnegativeSet b).card from finrank_onCoordinates _] at aV
  rw [eW, show finrank K W = (nonpositiveSet b).card from finrank_onCoordinates _] at aW
  change finrank K E=6 ∧ finrank K F=2 at r
  have sV := neg_card_add_nonnegative (b:=b)
  have sW := neg_card_add_ghost (b:=b)
  change 2≤(negativeSet b).card+finrank K ↥(F⊓U) ∧
    (negativeSet b).card+(ghostSet b).card≤2+finrank K ↥(F⊓U)
  omega

theorem exactly_two_negatives_of_all_active (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (hn : ∀ i,A i i≠0) (hact : ∀ i,b i≠0) : (negativeSet b).card=2 := by
  have ghost0 : ghostSpace b = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have e : x=0 := funext (fun i => mem_ghostSpace.mp hx i (hact i))
    rw [e]
    exact Submodule.zero_mem _
  have r := signed_ghost_census ho ha hn
  rw [ghost0,inf_bot_eq,finrank_bot] at r
  omega

theorem cubic_hidden_of_nonnegative (ho : HasOrder 7 A b) (hb : ∀ i,0≤b i) :
    zeroSpace A 3 ≤ ghostSpace b := by
  intro x hx
  apply ghost_of_nonnegative_mask_square_zero (x:=x)
  · apply mem_onCoordinates.mpr
    intro i hi
    exact (hi (by simp [nonnegativeSet,hb i])).elim
  · exact paid_pair_zero ho (by decide : 3+3+1≤7) hx (zeroSpace_le_treeSpace _ _ hx)

end Ordered

end
end RKResearch.Certified.Graded.SDIRKSeven
