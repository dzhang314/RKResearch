module
public import RKCert.ReviewedNative.ERK8PaidArithmetic
public import RKCert.ReviewedNative.GradedGrowth
public import RKCert.ReviewedNative.GradedPrefix
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Chronological debut on the single-defect-clock chart

All columns are evaluated on the reviewed tableau itself. The original
strict triangularity, not the numerical order of the clocks, determines
the first nonzero state. -/
namespace RKResearch.Certified.Graded.OneOff.PaidProof
open RKResearch Module
open scoped Classical Matrix

variable {K : Type*} [Field K] [EightUnits K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- Unit normalization of the canonical denominator-cleared native defect. -/
noncomputable def mDef (A : Matrix (Fin s) (Fin s) K) (j : ℕ) : Fin s → K :=
  ((j+1:ℕ):K)⁻¹ • monomialStageDefect A j

noncomputable def g (A : Matrix (Fin s) (Fin s) K) : Fin s → K := mDef A 1
noncomputable def h (A : Matrix (Fin s) (Fin s) K) : Fin s → K := mat A (g A)

omit [EightUnits K] in
theorem mat_g (A : Matrix (Fin s) (Fin s) K) : mat A (g A) = h A := rfl

omit [EightUnits K] in
theorem mDef_mem (A : Matrix (Fin s) (Fin s) K) (j : ℕ) :
    mDef A j ∈ zeroSpace A (j+1) :=
  (zeroSpace A (j+1)).smul_mem _ (monomialStageDefect_mem A j)

theorem mDef_apply (A : Matrix (Fin s) (Fin s) K) (j : ℕ) (i : Fin s) (bound : j+1≤8 := by omega) :
    mDef A j i = mat A ((nodes A)^j) i - nodes A i^(j+1)/((j+1:ℕ):K) := by
  have hunit : ((j+1:ℕ):K) ≠ 0 := (lowCastUnit (j+1) (by omega) bound).ne_zero
  change ((j+1:ℕ):K)⁻¹ *
    ((((j+1:ℕ):K) * mat A ((nodes A)^j) i) - nodes A i ^ (j+1)) = _
  rw [mul_sub,←mul_assoc,inv_mul_cancel₀ hunit,one_mul,div_eq_mul_inv,mul_comm (_⁻¹)]

theorem mDef_apply1 (A : Matrix (Fin s) (Fin s) K) (i : Fin s) :
    mDef A 1 i = mat A ((nodes A)^1) i - nodes A i ^ 2/2 :=
  mDef_apply A 1 i (by decide)

theorem mDef_apply2 (A : Matrix (Fin s) (Fin s) K) (i : Fin s) :
    mDef A 2 i = mat A ((nodes A)^2) i - nodes A i ^ 3/3 :=
  mDef_apply A 2 i (by decide)

theorem mDef_apply3 (A : Matrix (Fin s) (Fin s) K) (i : Fin s) :
    mDef A 3 i = mat A ((nodes A)^3) i - nodes A i ^ 4/4 :=
  mDef_apply A 3 i (by decide)

theorem mDef_apply4 (A : Matrix (Fin s) (Fin s) K) (i : Fin s) :
    mDef A 4 i = mat A ((nodes A)^4) i - nodes A i ^ 5/5 :=
  mDef_apply A 4 i (by decide)

theorem g_apply (A : Matrix (Fin s) (Fin s) K) (i : Fin s) :
    g A i = mat A (nodes A) i - nodes A i^2/2 := by
  simpa [g] using mDef_apply A 1 i

/-- The distinct physical clocks carrying a nonzero quadratic defect. -/
noncomputable def offKnots (A : Matrix (Fin s) (Fin s) K) : Finset K :=
  (Finset.univ.filter (fun i => g A i ≠ 0)).image (nodes A)

omit [EightUnits K] in
theorem mem_offKnots {x : K} :
    x ∈ offKnots A ↔ ∃ i, g A i ≠ 0 ∧ nodes A i = x := by
  simp [offKnots]

/-- Data of the earliest nonzero clock, which necessarily carries the
initial nonzero defect and identifies the unique support clock. -/
structure Origin (A : Matrix (Fin s) (Fin s) K) (a : K) (i : Fin s) : Prop where
  a_ne : a ≠ 0
  node : nodes A i = a
  earlier_node : ∀ j, j < i → nodes A j = 0
  defect : g A i = -a^2/2
  earlier_defect : ∀ j, j < i → g A j = 0
  off_support : ∀ j, g A j ≠ 0 → nodes A j = a

theorem origin_of_single_off (ha : ∀ i j, i ≤ j → A i j = 0)
    (hN : (offKnots A).card = 1)
    (hex : ∃ i, nodes A i≠0) : ∃ (a : K) (i : Fin s), Origin A a i := by
  let S : Set (Fin s) := {i | nodes A i≠0}
  obtain ⟨i,hi,hmin⟩ := wellFounded_lt.has_min S (show S.Nonempty from hex)
  have pre (j : Fin s) (hj : j < i) : nodes A j=0 := by
    by_contra x
    exact hmin j x hj
  let a := nodes A i
  change a≠0 at hi
  have gi : g A i = -a^2/2 := by
    rw [g_apply,causal_mat ha i _ pre]
    change 0-a^2/2 = _
    eight_ring K
  have ng : g A i≠0 := by
    rw [gi]
    exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ hi)) (by eight_num)
  have pG (j : Fin s) (hj : j < i) : g A j=0 := by
    rw [g_apply,causal_mat ha j _ (fun k hk => pre k (hk.trans hj)),pre j hj]
    simp
  obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hN
  have u : a∈offKnots A := mem_offKnots.mpr ⟨i,ng,rfl⟩
  have vu : a=v := by simpa [hv] using u
  refine ⟨a,i,⟨hi,rfl,pre,gi,pG,fun j hgj => ?_⟩⟩
  have e : nodes A j ∈ offKnots A := mem_offKnots.mpr ⟨j,hgj,rfl⟩
  simpa [hv,vu] using e

theorem Origin.g_ne {a : K} {i : Fin s} (O : Origin A a i) : g A i≠0 := by
  rw [O.defect]
  exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ O.a_ne)) (by eight_num)

omit [EightUnits K] in
theorem Origin.h_first {a : K} {i : Fin s} (ha : ∀ i j, i ≤ j → A i j = 0) (O : Origin A a i) :
    h A i = 0 := causal_mat ha i _ O.earlier_defect

omit [EightUnits K] in
theorem Origin.g_clock {a : K} {i : Fin s} (O : Origin A a i) :
    diag (nodes A) (g A)=a • g A := by
  ext j
  by_cases hj : g A j=0
  · simp [diag_apply,hj]
  · simp [diag_apply,O.off_support j hj]

theorem Origin.mDef_first {a : K} {i : Fin s} (ha : ∀ i j, i ≤ j → A i j = 0) (O : Origin A a i)
    {j : ℕ} (hj : j≠0) (bound : j+1≤8 := by omega) : mDef A j i = -a^(j+1)/((j+1:ℕ):K) := by
  rw [mDef_apply A j i bound,causal_mat ha i _ (fun k hk => by simp [O.earlier_node k hk,hj]),O.node]
  eight_ring K

/-- The causal quadratic seed is twice the normalized defect column. -/
theorem forward_seed_eq (A : Matrix (Fin s) (Fin s) K) :
    (2:K) • mat A (diag (nodes A) (1 : Fin s → K)) -
      diag (nodes A) (diag (nodes A) 1) = (2:K) • g A := by
  have he : diag (nodes A) (1 : Fin s → K) = nodes A := by ext i; simp
  rw [he]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, diag_apply]
  rw [g_apply]
  eight_ring K

/-- The independent primitive (Ag) is forced by explicitness. This does
not presume the one-off amplitude is constant, nor eliminate repeated rows. -/
theorem h_not_in_g_span (ha : ∀ i j, i ≤ j → A i j = 0) (hsep : ∀ a, coeffEval A 3 a ∈ zeroSpace A 3 → a = 0)
    {a : K} {i : Fin s} (O : Origin A a i) :
    h A ∉ Submodule.span K {g A} := by
  intro hDep
  obtain ⟨ξ,eq⟩ := Submodule.mem_span_singleton.mp hDep
  have e := congrFun eq i
  simp only [Pi.smul_apply,smul_eq_mul,O.h_first ha] at e
  have x0 : ξ=0 := (mul_eq_zero.mp e).resolve_right O.g_ne
  have h0 : h A=0 := by rw [←eq,x0,zero_smul]
  let U : Submodule K (Fin s → K) := Submodule.span K {g A}
  have gm : g A∈U := Submodule.mem_span_singleton_self _
  have hu : U ≤ zeroSpace A 3 := (Submodule.span_singleton_le_iff_mem ..).mpr
    (zeroSpace_mono A (by decide) (mDef_mem A 1))
  have h1 : diag (nodes A) (1:Fin s → K) = nodes A := by ext j; simp
  apply nodes_not_defect_of_separation (by decide) hsep
  apply hu
  rw [←h1]
  apply mem_of_invariant_seed (Equiv.refl _) (mat A) (causal_mat ha) (nodes A) 1 U
  · intro v hv
    obtain ⟨e,rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul,show mat A (g A)=0 from h0,smul_zero]
    exact U.zero_mem
  · intro v hv
    obtain ⟨e,rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul,O.g_clock]
    exact U.smul_mem _ (U.smul_mem _ gm)
  · rw [forward_seed_eq]
    exact U.smul_mem _ gm

theorem rank_two_span (ha : ∀ i j, i ≤ j → A i j = 0) (hsep : ∀ a, coeffEval A 3 a ∈ zeroSpace A 3 → a = 0) (rank : finrank K (zeroSpace A 3)=2)
    {a : K} {i : Fin s} (O : Origin A a i) :
    zeroSpace A 3=Submodule.span K {g A, h A} := by
  have gn : g A≠0 := fun e => O.g_ne (by rw [e]; rfl)
  have gm : g A∈zeroSpace A 3 := zeroSpace_mono A (by decide) (mDef_mem A 1)
  have hm : h A∈zeroSpace A 3 := mat_zeroSpace_bounded A 2 (mDef_mem A 1)
  rw [Submodule.span_insert]
  symm
  apply Submodule.eq_of_le_of_finrank_le
    (sup_le ((Submodule.span_singleton_le_iff_mem ..).mpr gm) ((Submodule.span_singleton_le_iff_mem ..).mpr hm))
  have r := Submodule.finrank_sup_span_singleton (h_not_in_g_span ha hsep O)
  rw [finrank_span_singleton gn] at r
  change finrank K (zeroSpace A 3) ≤ finrank K
    ((Submodule.span K {g A} ⊔ Submodule.span K {h A}) : Submodule K (Fin s → K))
  rw [rank,r]

theorem quadratic_defect_form (ha : ∀ i j, i ≤ j → A i j = 0) (hsep : ∀ a, coeffEval A 3 a ∈ zeroSpace A 3 → a = 0) (rank : finrank K (zeroSpace A 3)=2)
    {a : K} {i : Fin s} (O : Origin A a i) :
    ∃ lam : K, mDef A 2=(2*a/3) • g A + lam • h A := by
  have hm := mDef_mem A 2
  rw [rank_two_span ha hsep rank O] at hm
  obtain ⟨ξ,lam,e⟩ := Submodule.mem_span_pair.mp hm
  have ep := congrFun e.symm i
  have hi := O.mDef_first ha (j:=2) (by decide)
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hi,O.defect,O.h_first ha,
    mul_zero,add_zero,Nat.reduceAdd,Nat.cast_ofNat] at ep
  have hx : ξ=2*a/3 := by
    apply mul_right_cancel₀ (div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 O.a_ne))
      (by eight_num) : -a^2/2 ≠ 0)
    linear_combination (norm := eight_ring K) -ep
  exact ⟨lam,hx ▸ e.symm⟩

section Prefix
variable {k : ℕ}

omit [EightUnits K] in
theorem nodes_prefix (ha : ∀ i j, i ≤ j → A i j = 0) (hk : k ≤ s) :
    nodes (prefixMatrix A hk) = prefixRestrict hk (nodes A) :=
  prefix_mulVec ha hk 1

/-- Normalized residuals agree exactly with restricted residuals of the
original coefficients, including at repeated numerical clocks. -/
theorem mDef_prefix (ha : ∀ i j, i ≤ j → A i j = 0) (hk : k ≤ s) (j : ℕ) (bound : j+1≤8 := by omega) :
    mDef (prefixMatrix A hk) j = prefixRestrict hk (mDef A j) := by
  have hp : nodes (prefixMatrix A hk) ^ j = prefixRestrict hk (nodes A ^ j) := by
    rw [nodes_prefix ha hk]
    rfl
  ext i
  rw [mDef_apply _ _ _ bound, prefixRestrict_apply, mDef_apply _ _ _ bound, hp]
  have ha' := congrFun (prefix_mulVec ha hk (nodes A ^ j)) i
  change mat (prefixMatrix A hk) (prefixRestrict hk (nodes A ^ j)) i =
    mat A (nodes A ^ j) (Fin.castLE hk i) at ha'
  rw [ha', nodes_prefix ha hk, prefixRestrict_apply]

theorem h_prefix (ha : ∀ i j, i ≤ j → A i j = 0) (hk : k ≤ s) :
    h (prefixMatrix A hk) = prefixRestrict hk (h A) := by
  change mat (prefixMatrix A hk) (mDef (prefixMatrix A hk) 1) =
    prefixRestrict hk (mat A (g A))
  rw [mDef_prefix ha hk 1]
  exact prefix_mulVec ha hk _

end Prefix
end RKResearch.Certified.Graded.OneOff.PaidProof
